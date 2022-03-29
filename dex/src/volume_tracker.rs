//! `VolumeTracker` tracks total volume for the trailing *epoch*. The total is updated every *period*.
//!  
//! Notes:
//! - All timestamps in seconds
//!
//! TODO:
//! -[x] Decimals
//! -[ ] Proper timestamps
//! -[ ] Handle out of order timestamps
//! -[x] Make epoch length a constant instead of hard-coding to hours
//! -[x] Port to Serum DEX

use crate::{
    error::{DexErrorCode, DexResult, SourceFileId},
    fractional::Fractional,
};

declare_check_assert_macros!(SourceFileId::Matching);

// Number of periods in an epoch
const PERIODS_PER_EPOCH: usize = 30 * 24;
// Period = 1 hour
const SECONDS_PER_PERIOD: usize = 3600;
const SECONDS_PER_EPOCH: usize = PERIODS_PER_EPOCH * SECONDS_PER_PERIOD;
// const EPOCH_HOURS: usize = EPOCH_LEN * PERIOD_HOURS;
// const TRAILING_HOURS: usize = 30 * 24;
const VOLUME_BUFF_LEN: usize = PERIODS_PER_EPOCH;

#[derive(Debug, Default, Copy, Clone)]
#[repr(packed)]
struct VolumeEntry {
    timestamp: u64,
    volume: u64,
}

/// Circular buffer to store VolumeEntry items
#[repr(packed)]
#[derive(Copy, Clone)]
struct VolumeBuffer {
    /// Index of the last (most recent) entry
    last: usize,
    /// Index of the first (least recent) entry
    first: usize,
    /// Number of entries in the buffer
    len: usize,
    /// Buffer of volume entries
    buff: [VolumeEntry; VOLUME_BUFF_LEN],
}

impl VolumeBuffer {
    /// Create an empty VolumeBuffer
    fn new() -> Self {
        Self {
            buff: [VolumeEntry::default(); VOLUME_BUFF_LEN],
            last: 0,
            first: 0,
            len: 0,
        }
    }

    /// Returns an Option containing the first (least recent) entry. If the buffer is empty, returns None.
    fn get_first(&self) -> Option<VolumeEntry> {
        if self.len() > 0 {
            Some(self.buff[self.first])
        } else {
            None
        }
    }

    /// Get the last (most recent) entry
    fn get_last(&self) -> Option<VolumeEntry> {
        if self.len() > 0 {
            Some(self.buff[self.last])
        } else {
            None
        }
    }

    /// Get the number of entries in the buffer
    fn len(&self) -> usize {
        self.len
    }

    /// Increment the first index
    fn increment_first(&mut self) {
        self.first = Self::increment(self.first);
    }

    /// Increment the last index
    fn increment_last(&mut self) {
        self.last = Self::increment(self.last);
    }

    /// Increment an index; if the index exceeds the buffer size go back to 0
    fn increment(val: usize) -> usize {
        if val == VOLUME_BUFF_LEN - 1 {
            0
        } else {
            val + 1
        }
    }

    /// Push an entry onto the buffer. Returns `Ok(Some(overwritten_value))` if
    /// the first value was overwritten, otherwise `Ok(None)`. Returns
    /// `Err(msg)` if the buffer is full and `overwrite = false`.
    ///
    /// # Arguments
    ///
    /// * `entry` - The `VolumeEntry` to add the the buffer.
    /// * `overwrite` - Flag representing whether the buffer should overwrite the first entry if it is full.
    fn push(&mut self, entry: VolumeEntry, overwrite: bool) -> DexResult<Option<VolumeEntry>> {
        let mut res: Option<VolumeEntry> = None;
        if self.len() == VOLUME_BUFF_LEN {
            if overwrite {
                // pop the first (oldest)
                res = self.pop();
                if res.is_none() {
                    unreachable!("If the buffer is full, self.pop() should always return a value.")
                }
            } else {
                return Err(DexErrorCode::VolumeBufferOverflow.into());
            }
        }
        if self.len() != 0 {
            // If the buffer is not empty, increment self.last
            self.increment_last();
        }
        // Add the new entry
        self.buff[self.last] = entry;
        self.len += 1;
        Ok(res)
    }

    /// Removes the first (least recent) entry and returns it. If the buffer is empty, returns None.
    fn pop(&mut self) -> Option<VolumeEntry> {
        if self.len() == 0 {
            None
        } else {
            let popped = self.buff[self.first];
            self.buff[self.first] = VolumeEntry::default();
            self.increment_first();
            self.len -= 1;
            Some(popped)
        }
    }

    /// Pop all entries with timestamp < `min_ts`
    fn pop_to_ts(&mut self, min_ts: u64) -> Vec<VolumeEntry> {
        let mut popped: Vec<VolumeEntry> = Vec::new();
        if self.len() == 0 {
            return popped;
        }
        let mut first = self.buff[self.first];
        while self.len() > 0 && first.timestamp < min_ts {
            if let Some(ve) = self.pop() {
                popped.push(ve);
            } else {
                return popped;
            }
            first = self.buff[self.first];
        }
        popped
    }

    fn sum_volume(&self) -> u64 {
        self.buff.iter().map(|ve| ve.volume).sum()
    }
}

/// Invariants:
///     period_start_ts <= period_volume.timestamp
///     history.first().timestamp <= period_start_ts - 3600 * TRAILING_HOURS
///     history.last().timestamp < last_recalc_ts
///     total_trailing_volume = sum(history.buff.iter().map(|ve| ve.volume))
#[repr(packed)]
#[derive(Copy, Clone)]
pub struct VolumeTracker {
    /// Buffer of volume entries used to calculate `total_trailing_volume`.
    /// Volumes in the buffer should all have timestamps in the range
    /// `[period_start_ts - SECONDS_PER_EPOCH, period_start_ts)`
    history: VolumeBuffer,
    /// Volume for the current period, starting at `period_start_ts`
    period_volume: VolumeEntry,
    /// The ts of the start of the current period. The total epoch volume is recalculated when the period rolls over.
    period_start_ts: u64,
    /// The total volume over the trailing `EPOCH_LEN` periods, as of `period_start_ts`
    total_trailing_volume: u64,
    /// The trailing decimals of the volume
    decimals: u8,
}

impl VolumeTracker {
    pub fn new(timestamp: u64) -> Self {
        Self {
            history: VolumeBuffer::new(),
            period_volume: VolumeEntry::default(),
            period_start_ts: timestamp,
            total_trailing_volume: 0,
            // Hard-code decimals for now
            decimals: 9,
        }
    }

    /// Adds a quantity to the tracker; returns `Some(total_trailing_volume)` if it has been recalculated, otherwise returns `None`.
    pub fn add(&mut self, timestamp: u64, quantity: u64) -> DexResult<Option<u64>> {
        let s_since_period_start = timestamp - self.period_start_ts;
        let mut res: Option<u64> = None;
        if s_since_period_start >= 3600 {
            // Set start of period to the most recent period boundary
            self.period_start_ts = timestamp - (s_since_period_start % SECONDS_PER_PERIOD as u64);
            let epoch_start_ts = self.period_start_ts - SECONDS_PER_EPOCH as u64;
            // Push current volume to buffer
            self.history.push(self.period_volume, true)?;
            // Reset current volume to zero
            self.period_volume.volume = 0;
            // Clean up old buffer entries
            self.history.pop_to_ts(epoch_start_ts);
            res = Some(self.update_total());
        }
        // Update current volume
        // TODO: what if timestamp < current_volume.timestamp?
        self.period_volume.volume += quantity;
        self.period_volume.timestamp = timestamp;
        Ok(res)
    }
    /// Adds a fractional quantity to the tracker; returns
    /// `Some(total_trailing_volume)` if it has been recalculated, otherwise
    /// returns `None`.
    pub fn add_fractional(
        &mut self,
        timestamp: u64,
        quantity: Fractional,
    ) -> DexResult<Option<Fractional>> {
        check_assert!(!quantity.is_negative())?;
        // Always round number of decimals to `self.decimals`
        let native_quantity = if quantity.exp != self.decimals as u64 {
            quantity.round(self.decimals as u32)?.m
        } else {
            quantity.m
        };
        self.add(timestamp, native_quantity as u64)
            .map(|opt| opt.map(|amt| Fractional::new(amt as i64, self.decimals as u64)))
    }

    fn update_total(&mut self) -> u64 {
        self.total_trailing_volume = self.history.sum_volume();
        self.total_trailing_volume
    }

    pub fn get_total(&self) -> u64 {
        self.total_trailing_volume
    }

    pub fn get_period_volume(&self) -> u64 {
        self.period_volume.volume
    }

    pub fn get_period_volume_fractional(&self) -> Fractional {
        Fractional::new(self.period_volume.volume as i64, self.decimals as u64)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::time::SystemTime;

    // Wrapper to avoid unaligned reference error
    fn assert_eq(left: u64, right: u64) {
        assert_eq!(left, right)
    }

    #[test]
    fn test_volume_buffer() {
        let mut vb = VolumeBuffer::new();
        let now = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        // Fill the buffer
        for i in 0..VOLUME_BUFF_LEN {
            let ve = VolumeEntry {
                timestamp: now + i as u64,
                volume: i as u64,
            };
            let res = vb.push(ve, true).unwrap();
            // Pushing up to the max capacity should not overwrite; result should be None
            assert!(res.is_none());
            // Check length
            assert_eq!(vb.len(), i + 1);
        }
        // Check first and last entries
        // Annoyingly necessary to bind volume to a variable before passing into `assert_eq` to avoid unaligned reference
        assert_eq(vb.get_first().unwrap().volume, 0);
        assert_eq(vb.get_last().unwrap().volume, (VOLUME_BUFF_LEN - 1) as u64);
        let ve = VolumeEntry {
            timestamp: SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            volume: VOLUME_BUFF_LEN as u64,
        };
        // Test overflow logic
        vb.push(ve, false)
            .expect_err("Expected buffer overflow error.");
        let res = vb.push(ve, true).unwrap();
        assert!(matches!(res, Some(e) if e.volume == 0));
        assert_eq(vb.get_first().unwrap().volume, 1);
        assert_eq(vb.get_last().unwrap().volume, (VOLUME_BUFF_LEN) as u64);
        // Length should stay the same since we are overwriting
        assert_eq!(vb.len(), VOLUME_BUFF_LEN);

        // Pop all elements with ts < min_ts
        let min_ts = vb.buff[VOLUME_BUFF_LEN / 2 + 1].timestamp;
        let popped = vb.pop_to_ts(min_ts);
        assert_eq!(popped.len(), VOLUME_BUFF_LEN / 2);
        assert_eq!(vb.len(), VOLUME_BUFF_LEN / 2);
        assert_eq(vb.get_first().unwrap().timestamp, min_ts);

        // Pop all elements from the buffer
        for i in VOLUME_BUFF_LEN / 2..VOLUME_BUFF_LEN {
            let res = vb.pop().unwrap();
            // Pushing up to the max capacity should not overwrite; result should be None
            assert!(res.volume == (i + 1) as u64);
            // Check length
            assert_eq!(vb.len(), VOLUME_BUFF_LEN - 1 - i);
        }
        assert!(vb.pop().is_none())
    }

    #[test]
    fn test_volume_tracker() {
        let start = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        let mut vt = VolumeTracker::new(start);
        assert_eq!(vt.get_total(), 0);

        // 1st hour: 200 units of volume
        // Total == 0
        let mut now = start + 60;
        assert!(vt.add(now, 100).unwrap().is_none());
        assert_eq!(vt.get_total(), 0);
        now += 60;
        assert!(vt.add(now, 100).unwrap().is_none());
        assert_eq!(vt.get_total(), 0);

        // 2nd hour: 100 units of volume
        // Total == 200
        now = start + 3600;
        let t = vt.add(now, 100).unwrap().unwrap();
        assert_eq!(t, 200);
        assert_eq!(vt.get_total(), 200);

        // 3rd hour: 200 units of volume
        // Total == 300
        now += 4200;
        let t = vt.add(now, 200).unwrap().unwrap();
        assert_eq!(t, 300);
        assert_eq!(vt.get_total(), 300);

        // 721st hour: 100 units of volume
        // Total == 500
        now = start + 720 * 3600;
        let t = vt.add(now, 100).unwrap().unwrap();
        assert_eq!(t, 500);
        assert_eq!(vt.get_total(), 500);

        // 722nd hour: 200 units of volume
        // Total == 400
        now = start + 721 * 3600;
        let t = vt.add(now, 200).unwrap().unwrap();
        assert_eq!(t, 400);
        assert_eq!(vt.get_total(), 400);

        // 723rd hour: 100 units of volume
        // Total == 500
        now = start + 722 * 3600;
        let t = vt.add(now, 100).unwrap().unwrap();
        assert_eq!(t, 500);
        assert_eq!(vt.get_total(), 500);

        // 1444th hour: 100 units of volume
        // Total == 0
        now = start + 1443 * 3600;
        let t = vt.add(now, 100).unwrap().unwrap();
        assert_eq!(t, 0);
        assert_eq!(vt.get_total(), 0);

        // Test add_fractional
        let pv = vt.get_period_volume_fractional();
        assert_eq!(pv.m as i64, 100);

        vt.add_fractional(now + 1, Fractional::new(12300, 3))
            .unwrap();
        let pv = vt.get_period_volume_fractional();

        assert_eq!(pv.m, 12_300_000_100);
        assert_eq!(pv.exp, vt.decimals as u64);
        assert_eq!(format!("{}", pv), "12.300000100".to_string());
    }
}

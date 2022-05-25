use std::str::FromStr;

use solana_program::pubkey::Pubkey;

pub const SOL_MINT: &str = "So11111111111111111111111111111111111111112";
pub const USDC_MINT: &str = "EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v";

pub const SOL_USD_PRICE: &str = "H6ARHf6YXhGYeQfUzQNGk6rDNnLBQKrenN712K4AQJEG";
pub const USDC_USD_PRICE: &str = "Gnt27xtC473ZT2Mw5u8wZ68Z3gULkSTb5DuxJy7eJotD";

pub fn get_price_account_for_mint(mint: &Pubkey) -> Option<Pubkey> {
    let mint_str = mint.to_string();
    if mint_str == SOL_MINT {
        Some(Pubkey::from_str(SOL_USD_PRICE).unwrap())
    } else if mint_str == USDC_MINT {
        Some(Pubkey::from_str(USDC_USD_PRICE).unwrap())
    } else {
        None
    }
}

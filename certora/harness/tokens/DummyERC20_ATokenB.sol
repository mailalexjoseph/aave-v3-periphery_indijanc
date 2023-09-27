// SPDX-License-Identifier: MIT
pragma solidity ^0.8.10;

import "./DummyERC20_AToken.sol";

contract DummyERC20_ATokenB is DummyERC20_AToken {
    
    constructor(
    IPool pool,
    string memory name,
    string memory symbol,
    uint8 decimals
  ) DummyERC20_AToken(pool, name, symbol, decimals) {
    // Intentionally left blank
  }
}
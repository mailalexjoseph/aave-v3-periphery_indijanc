// SPDX-License-Identifier: MIT
pragma solidity ^0.8.10;

import {MintableIncentivizedERC20} from "@aave/core-v3/contracts/protocol/tokenization/base/MintableIncentivizedERC20.sol";
import {IPool} from '@aave/core-v3/contracts/interfaces/IPool.sol';

contract DummyERC20_AToken is MintableIncentivizedERC20 {
    
      constructor(
    IPool pool,
    string memory name,
    string memory symbol,
    uint8 decimals
  ) MintableIncentivizedERC20(pool, name, symbol, decimals) {
    // Intentionally left blank
  }

    function scaledTotalSupply() public view returns (uint256) {
        return super.totalSupply();
    }

    function scaledBalanceOf(address account) public view returns (uint256) {
        return super.balanceOf(account);
    }

    function getScaledUserBalanceAndSupply(address account) public view returns (uint256, uint256){
        return (scaledBalanceOf(account), scaledTotalSupply());
    }

    function mint(address account, uint128 amount) external {
        _mint(account, amount);
    }

    function burn(address account, uint128 amount) external {
        _burn(account, amount);
    }
}
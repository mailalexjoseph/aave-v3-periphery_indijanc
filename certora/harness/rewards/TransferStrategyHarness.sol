
pragma solidity ^0.8.10;

import {IERC20} from '@aave/core-v3/contracts/dependencies/openzeppelin/contracts/IERC20.sol';

contract TransferStrategyHarness {

    IERC20 public REWARD;

    // executes the actual transfer of the reward to the receiver.
    // This contract also act as the rewards vault
    function performTransfer(
        address to,
        address reward,
        uint256 amount
    ) external returns (bool){
        require(reward == address(REWARD));
        return REWARD.transfer(to, amount);
    }
}
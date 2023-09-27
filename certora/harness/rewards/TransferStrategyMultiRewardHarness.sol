
pragma solidity ^0.8.10;

import {IERC20} from '@aave/core-v3/contracts/dependencies/openzeppelin/contracts/IERC20.sol';

contract TransferStrategyMultiRewardHarness {

    // executes the actual transfer of the rewards to the receiver
    function performTransfer(
        address to,
        address reward,
        uint256 amount
    ) external returns (bool){
        return IERC20(reward).transfer(to, amount);
    }
}
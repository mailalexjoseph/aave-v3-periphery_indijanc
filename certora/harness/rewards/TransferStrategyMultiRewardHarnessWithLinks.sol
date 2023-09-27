
pragma solidity ^0.8.10;

import {IERC20} from '@aave/core-v3/contracts/dependencies/openzeppelin/contracts/IERC20.sol';

contract TransferStrategyMultiRewardHarnessWithLinks {

    IERC20 public REWARD;
    IERC20 public REWARD_B;
    // you can add more rewards

    // executes the actual transfer of the rewards to the receiver
    function performTransfer(
        address to,
        address reward,
        uint256 amount
    ) external returns (bool){
        
        require(reward == address(REWARD) || reward == address(REWARD_B));
        
        if (reward == address(REWARD)){
            return REWARD.transfer(to, amount);
        }
        else if (reward == address(REWARD_B)){
            return REWARD_B.transfer(to, amount);
        }
        return false;
    }
}
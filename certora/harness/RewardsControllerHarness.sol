// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.10;

import {RewardsController} from '../../contracts/rewards/RewardsController.sol';
import {IScaledBalanceToken} from '../../node_modules/@aave/core-v3/contracts/interfaces/IScaledBalanceToken.sol';

contract RewardsControllerHarness is RewardsController {
    
    constructor(address emissionManager) RewardsController(emissionManager) {}
    // returns an asset's reward index
    function getAssetRewardIndex(address asset, address reward) external view returns (uint256) {
        return _assets[asset].rewards[reward].index;
    }

    // returns the isRewardEnabled flag for the specific reward
    function isRewardEnabled(address reward) external view returns (bool) {
        return _isRewardEnabled[reward];
    }

    // returns the lastUpdateTimestamp for a given reward on a given asset
    function getLastUpdateTimestamp(address asset, address reward) external view returns (uint256 lastUpdateTimestamp) {
        (, , lastUpdateTimestamp, ) = getRewardsData(asset, reward);
    }

    function getAvailableRewardsCountByAsset(address asset) external view returns (uint256 count) {
        count = _assets[asset].availableRewardsCount;
    }

    function getAssetsList() external view returns (address[] memory retAssets) {
        retAssets = _assetsList;
    }

    function getAssetScaledTotalSupply(address asset) external view returns (uint256 totalSupply) {
        totalSupply = IScaledBalanceToken(asset).scaledTotalSupply();
    }

    function getUserDataByAssetByReward(address user, address asset, address reward) external view returns (uint256 index, uint256 accrued) {
        index = _assets[asset].rewards[reward].usersData[user].index;
        accrued = _assets[asset].rewards[reward].usersData[user].accrued;
    }
}
import "methods/Methods_base.spec";

using DummyERC20_rewardTokenB as RewardTokenB;
using TransferStrategyMultiRewardHarness as TransferStrategy;

methods {
  function RewardTokenB.balanceOf(address) external returns (uint256) envfree;
}

///////////////// Properties ///////////////////////


// claimAllRewards should always transfer up to eligible amount
rule claimAllRewardsSendsEligibleAmount(method f) {
    
    env e;
    address[] assets;
    requireSingleAddressInList(assets, AToken);

    // Limit to single asset and two reward tokens
    requireSingleAddressInList(getAssetsList(), AToken);
    requireDoubleRewardForAsset(AToken, RewardToken, RewardTokenB);

    // Reduce scope to avoid timeouts
    require getAssetDecimals(AToken) == 18;
    require getLastUpdateTimestamp(AToken, RewardToken) == e.block.timestamp;
    require getLastUpdateTimestamp(AToken, RewardTokenB) == e.block.timestamp;
    address anyRewardToken;
    require getUserRewards(e, assets, e.msg.sender, anyRewardToken) > 0 => anyRewardToken == RewardToken || anyRewardToken == RewardTokenB;

    // mark reward token balance of user
    uint256 userBalanceBefore = RewardToken.balanceOf(e.msg.sender);
    // mark reward tokenB balance of user
    uint256 userBalanceBeforeB = RewardTokenB.balanceOf(e.msg.sender);
    // mark rewards of user
    uint256 userRewards = getUserRewards(e, assets, e.msg.sender, RewardToken);
    uint256 userRewardsB = getUserRewards(e, assets, e.msg.sender, RewardTokenB);
    require e.msg.sender != TransferStrategy;

    claimAllRewards(e, assets, e.msg.sender);

    // mark reward tokens balance of user after transaction
    uint256 userBalanceAfter = RewardToken.balanceOf(e.msg.sender);
    uint256 userBalanceAfterB = RewardTokenB.balanceOf(e.msg.sender);
    // if user reward token balances increased, they must have been eligible for the amount
    assert userBalanceAfter > userBalanceBefore => userRewards >= assert_uint256(userBalanceAfter - userBalanceBefore);
    //assert userBalanceAfterB > userBalanceBeforeB => userRewardsB >= assert_uint256(userBalanceAfterB - userBalanceBeforeB);
}
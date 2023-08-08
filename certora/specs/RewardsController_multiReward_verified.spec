import "methods/Methods_base.spec";

using DummyERC20_rewardTokenB as RewardTokenB;
using TransferStrategyMultiRewardHarnessWithLinks as TransferStrategy;

methods {
  function RewardTokenB.balanceOf(address) external returns (uint256) envfree;
}

///////////////// Properties ///////////////////////

// Claiming rewards with claimRewards() correctly reduces amount of accrued rewards of the user and transfers rewards
//  - with amount less than or equal to accrued rewards
rule claimRewardsUpdatesUserRewards() {
    
    env e;
    address targetUser;
    uint256 amount;
    address[] assets;
    // Limit to single asset and two reward tokens
    requireSingleAddressInList(assets, AToken);
    requireSingleAddressInList(getAssetsList(), AToken);
    requireDoubleRewardForAsset(AToken, RewardToken, RewardTokenB);

    uint256 targetUserRewardsBefore = getUserRewards(e, assets, e.msg.sender, RewardTokenB);
    require targetUser != TransferStrategy;
    require amount <= targetUserRewardsBefore;

    // Reduce scope to avoid timeouts
    require getAssetDecimals(AToken) == 18;
    require getLastUpdateTimestamp(AToken, RewardToken) == e.block.timestamp;
    require getLastUpdateTimestamp(AToken, RewardTokenB) == e.block.timestamp;

    claimRewards(e, assets, amount, targetUser, RewardTokenB);

    uint256 targetUserRewardsAfter = getUserRewards(e, assets, e.msg.sender, RewardTokenB);
    // The difference between before and after should be exactly the amount specified
    assert require_uint256(targetUserRewardsAfter + amount) == targetUserRewardsBefore;
}

// Claiming rewards with claimRewards() correctly sends the amount of rewards to target user
//  - with amount less than or equal to accrued rewards
rule claimRewardsSendsRewards() {
    
    env e;
    address targetUser;
    uint256 amount;
    address[] assets;
    // Limit to single asset and two reward tokens
    requireSingleAddressInList(assets, AToken);
    requireSingleAddressInList(getAssetsList(), AToken);
    requireDoubleRewardForAsset(AToken, RewardToken, RewardTokenB);

    require amount <= getUserRewards(e, assets, e.msg.sender, RewardTokenB);
    require targetUser != TransferStrategy;

    uint256 targetUserRewardBalanceBefore = RewardTokenB.balanceOf(targetUser);

    // Reduce scope to avoid timeouts
    require getAssetDecimals(AToken) == 18;
    require getLastUpdateTimestamp(AToken, RewardToken) == e.block.timestamp;
    require getLastUpdateTimestamp(AToken, RewardTokenB) == e.block.timestamp;

    claimRewards(e, assets, amount, targetUser, RewardTokenB);

    uint256 targetUserRewardBalanceAfter = RewardTokenB.balanceOf(targetUser);
    // Target user must have gotten the specified amount of reward tokens
    assert require_uint256(targetUserRewardBalanceBefore + amount) == targetUserRewardBalanceAfter;
}

// Claiming rewards with claimRewards() correctly reduces amount of accrued rewards of the user and transfers rewards
//  - with amount more than accrued rewards
rule claimRewardsUpdatesUserRewards_bigAmount() {
    
    env e;
    address targetUser;
    uint256 amount;
    address[] assets;
    // Limit to single asset and two reward tokens
    requireSingleAddressInList(assets, AToken);
    requireSingleAddressInList(getAssetsList(), AToken);
    requireDoubleRewardForAsset(AToken, RewardToken, RewardTokenB);

    uint256 targetUserRewardsBefore = getUserRewards(e, assets, e.msg.sender, RewardTokenB);
    require targetUser != TransferStrategy;
    require amount > targetUserRewardsBefore;

    // Reduce scope to avoid timeouts
    require getAssetDecimals(AToken) == 18;
    require getLastUpdateTimestamp(AToken, RewardToken) == e.block.timestamp;
    require getLastUpdateTimestamp(AToken, RewardTokenB) == e.block.timestamp;

    claimRewards(e, assets, amount, targetUser, RewardTokenB);

    // Rewards should be depleted
    assert 0 == getUserRewards(e, assets, e.msg.sender, RewardTokenB);
}

// Claiming rewards with claimRewards() correctly sends the amount of rewards to target user
//  - with amount more than accrued rewards
rule claimRewardsSendsRewards_bigAmount() {
    
    env e;
    address targetUser;
    uint256 amount;
    address[] assets;
    // Limit to single asset and two reward tokens
    requireSingleAddressInList(assets, AToken);
    requireSingleAddressInList(getAssetsList(), AToken);
    requireDoubleRewardForAsset(AToken, RewardToken, RewardTokenB);

    uint256 targetUserRewardsBefore = getUserRewards(e, assets, e.msg.sender, RewardTokenB);
    require targetUser != TransferStrategy;
    require amount > targetUserRewardsBefore;

    uint256 targetUserRewardBalanceBefore = RewardTokenB.balanceOf(targetUser);

    // Reduce scope to avoid timeouts
    require getAssetDecimals(AToken) == 18;
    require getLastUpdateTimestamp(AToken, RewardToken) == e.block.timestamp;
    require getLastUpdateTimestamp(AToken, RewardTokenB) == e.block.timestamp;

    claimRewards(e, assets, amount, targetUser, RewardTokenB);

    uint256 targetUserRewardBalanceAfter = RewardTokenB.balanceOf(targetUser);
    // Target user must have gotten all the remaining rewards
    assert require_uint256(targetUserRewardBalanceBefore + targetUserRewardsBefore) == targetUserRewardBalanceAfter;
}

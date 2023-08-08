import "methods/Methods_base.spec";

using DummyERC20_rewardTokenB as RewardTokenB;
using DummyERC20_ATokenB as ATokenB;
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

// Claiming the rewards with claimAllRewards() correctly reduces amount of accrued rewards of the user
rule claimAllRewardsUpdatesUserRewards() {
    
    env e;
    address targetUser;
    address[] assets;
    // Limit to single asset and two reward tokens
    requireSingleAddressInList(assets, AToken);
    requireSingleAddressInList(getAssetsList(), AToken);
    requireDoubleRewardForAsset(AToken, RewardToken, RewardTokenB);
    require targetUser != TransferStrategy;

    // Reduce scope to avoid timeouts
    require getAssetDecimals(AToken) == 18;
    require getLastUpdateTimestamp(AToken, RewardToken) == e.block.timestamp;
    require getLastUpdateTimestamp(AToken, RewardTokenB) == e.block.timestamp;

    claimAllRewards(e, assets, targetUser);
    uint256 senderRewardAfter = getUserRewards(e, assets, e.msg.sender, RewardToken);
    uint256 senderRewardBAfter = getUserRewards(e, assets, e.msg.sender, RewardTokenB);

    // Sender rewards should be depleted
    assert senderRewardAfter == 0;
    assert senderRewardBAfter == 0;
}

// Claiming the rewards with claimAllRewards() sends correct amount of reward tokens to receiver
rule claimAllRewardsSendsRewards() {
    
    env e;
    address targetUser;
    address[] assets;
    // Limit to single asset and two reward tokens
    requireSingleAddressInList(assets, AToken);
    requireSingleAddressInList(getAssetsList(), AToken);
    requireDoubleRewardForAsset(AToken, RewardToken, RewardTokenB);
    require targetUser != TransferStrategy;

    // require that target user doesn't have any reward tokens B - helps with timeouts
    uint256 targetUserRewardBBalanceBefore = RewardTokenB.balanceOf(targetUser);
    require targetUserRewardBBalanceBefore == 0;
    
    // mark the sender's rewards
    uint256 senderRewardBBefore = getUserRewards(e, assets, e.msg.sender, RewardTokenB);
    require targetUser != TransferStrategy;

    // Reduce scope to avoid timeouts
    require getAssetDecimals(AToken) == 18;
    require getLastUpdateTimestamp(AToken, RewardToken) == e.block.timestamp;
    require getLastUpdateTimestamp(AToken, RewardTokenB) == e.block.timestamp;

    claimAllRewards(e, assets, targetUser);

    // mark target user reward token B balance
    uint256 targetUserRewardBBalanceAfter = RewardTokenB.balanceOf(targetUser);

    // target user should now have all the claimed rewards
    assert senderRewardBBefore == targetUserRewardBBalanceAfter;
}

// Claiming the rewards with claimAllRewards() correctly reduces amount of accrued rewards of the user
//  - with two assets and same reward
rule claimAllRewardsForTwoAssetsUpdatesUserRewards() {
    
    env e;
    address targetUser;
    address[] assets;
    // Limit to two assets and single reward token
    requireDoubleAddressInList(assets, AToken, ATokenB);
    requireDoubleAddressInList(getAssetsList(), AToken, ATokenB);
    requireSingleRewardForAsset(AToken, RewardToken);
    requireSingleRewardForAsset(ATokenB, RewardToken);
    require targetUser != TransferStrategy;

    // Reduce scope to avoid timeouts
    require getAssetDecimals(AToken) == 18;
    require getAssetDecimals(ATokenB) == 18;
    require getLastUpdateTimestamp(AToken, RewardToken) == e.block.timestamp;
    require getLastUpdateTimestamp(ATokenB, RewardToken) == e.block.timestamp;

    claimAllRewards(e, assets, targetUser);
    uint256 senderRewardAfter = getUserRewards(e, assets, e.msg.sender, RewardToken);

    // Sender rewards should be depleted
    assert senderRewardAfter == 0;
}

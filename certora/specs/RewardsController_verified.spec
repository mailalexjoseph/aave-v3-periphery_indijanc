import "methods/Methods_base.spec";

using TransferStrategyHarness as TransferStrategy;

///////////////// Properties ///////////////////////

// lastUpdateTimestamp should never be in the future
invariant lastUpdateLessOrEqualToCurrentTimestamp(env e, address asset, address reward)
    getLastUpdateTimestamp(asset, reward) <= e.block.timestamp
    {
        preserved with (env e2) { require e.block.timestamp == e2.block.timestamp; }
    }

// If the lastUpdateTimestamp has ever been set, it must never be cleared (set to 0)
// Otherwise we would be able to insert duplicates of the same reward for a given asset
rule lastUpdateTimestampCannotBeSetToZero(method f) filtered { f -> !f.isView } {
    address asset;
    address reward;

    require getLastUpdateTimestamp(asset, reward) > 0;

    // verifying with all non-view functions
    env e;
    require e.block.timestamp > 0;
    calldataarg args;
    f(e, args);

    // Reward lastUpdateTimestamp must never be set back to 0
    assert getLastUpdateTimestamp(asset, reward) > 0;
}

// All configuration changes of the RewardsController are restricted to the emission manager
rule onlyEmissionManagerAllowed(method f) filtered { f -> !f.isView } {
    
    address anyReward;
    address anyUser;
    address anyAsset;

    // check state before
    bool rewardEnabledBefore = isRewardEnabled(anyReward);
    address claimerBefore = getClaimer(anyUser);
    address transferStrategyBefore = getTransferStrategy(anyReward);
    address rewardOracleBefore = getRewardOracle(anyReward);
    uint256 emissionPerSecondBefore;
    uint256 distributionEndBefore;
    _, emissionPerSecondBefore, _, distributionEndBefore = getRewardsData(anyAsset, anyReward);

    // verifying with all non-view functions
    env e;
    calldataarg args;
    f(e, args);

    // check state after
    bool rewardEnabledAfter = isRewardEnabled(anyReward);
    address claimerAfter = getClaimer(anyUser);
    address transferStrategyAfter = getTransferStrategy(anyReward);
    address rewardOracleAfter = getRewardOracle(anyReward);
    uint256 emissionPerSecondAfter;
    uint256 distributionEndAfter;
    _, emissionPerSecondAfter, _, distributionEndAfter = getRewardsData(anyAsset, anyReward);

    // asserts that check if any configuration has changed it must have been done by the emission manager
    assert rewardEnabledAfter != rewardEnabledBefore => e.msg.sender == EMISSION_MANAGER();
    assert claimerAfter != claimerBefore => e.msg.sender == EMISSION_MANAGER();
    assert transferStrategyAfter != transferStrategyBefore => e.msg.sender == EMISSION_MANAGER();
    assert rewardOracleAfter != rewardOracleBefore => e.msg.sender == EMISSION_MANAGER();
    assert emissionPerSecondAfter != emissionPerSecondBefore => e.msg.sender == EMISSION_MANAGER();
    assert distributionEndAfter != distributionEndBefore => e.msg.sender == EMISSION_MANAGER();
}

// Depleting users accrued rewards can only be done by the claim methods
rule depletingRewardsByClaim(method f) filtered { f -> !f.isView } {
    
    address anyUser;
    address reward;
    // require some user accrued rewards
    require getUserAccruedRewards(anyUser, reward) > 0;

    // verifying with all non-view functions
    env e;
    calldataarg args;
    f(e, args);

    // if the user has depleted rewards, it must have been done by one of the claim methods
    assert getUserAccruedRewards(anyUser, reward) == 0 => isClaimFunction(f);
}

// When someone claims, the rewards state must be updated:
//  - asset index increased
//  - asset lastUpdateTimestamp increased
//  - user index must be updated
rule claimingRewardsMustUpdateRewardsState(method f) filtered { f -> isClaimFunction(f) } {
    
    env e;
    address anyUser;
    // require a single configured asset and a single configured reward for that asset
    requireSingleAddressInList(getAssetsList(), AToken);
    requireSingleRewardForAsset(AToken, RewardToken);

    // There's several elements in RewardsData that need to be set to have a valid current active reward on the asset
    requireActiveReward(AToken, RewardToken, e);
    // require lastUpdateTimestamp to be less than or equal to current timestamp, 
    // property ensured by lastUpdateLessOrEqualToCurrentTimestamp invariant
    requireInvariant lastUpdateLessOrEqualToCurrentTimestamp(e, AToken, RewardToken);

    uint256 indexBefore;
    uint256 lastUpdateTimestampBefore;

    // define an environment that has a valid timestamp but is older than e
    env e_past;
    require e_past.block.timestamp > 0;
    require e_past.block.timestamp < e.block.timestamp;

    // use the older environment variable to get an index for the given asset/reward
    uint256 retIndex;
    _, retIndex = getAssetIndex(e_past, AToken, RewardToken);

    indexBefore, _, lastUpdateTimestampBefore, _ = getRewardsData(AToken, RewardToken);
    
    // the index in the precondition must have been generated in the past (from the env variable in the past),
    // hence using this require to force suitable precondition reward data
    require indexBefore == retIndex;
    
    // require that some time has past since last update
    require lastUpdateTimestampBefore < e.block.timestamp;

    // Depending on time difference, emissions per second, asset unit and scaled total supply of the Atoken,
    // the index increase may get rounded to 0 on division.
    // This require is here to avoid rounding on division without the need to properly set all mentioned
    // parameters and instead just set the denumerator to 1
    require getAssetScaledTotalSupply(AToken) == 1;

    uint256 userRewardsBefore = getUserAccruedRewards(anyUser, RewardToken);
    // require some user accrued rewards
    require userRewardsBefore > 0;

    // verifying with all claim functions
    calldataarg args;
    f(e, args);

    uint256 userRewardsAfter = getUserAccruedRewards(anyUser, RewardToken);

    // require that the user has claimed some rewards with any claim method
    require userRewardsAfter < userRewardsBefore;

    uint256 indexAfter;
    uint256 lastUpdateTimestampAfter;
    indexAfter, _, lastUpdateTimestampAfter, _ = getRewardsData(AToken, RewardToken);

    uint256 userIndex;
    userIndex, _ = getUserDataByAssetByReward(anyUser, AToken, RewardToken);

    // index must be updated
    assert indexAfter > indexBefore;
    // lastUpdateTimestamp must be updated
    assert lastUpdateTimestampAfter > lastUpdateTimestampBefore;
    // the user index must be properly set
    assert userIndex == indexAfter;
}

// There should be no way to send rewards to zero address, effectively burn them
rule cannotClaimToZeroAddress(method f) filtered { f -> !f.isView } {
    
    address zeroAddress = 0;
    // mark balance of zero address
    uint256 zeroAddressBalance = RewardToken.balanceOf(zeroAddress);

    env e;
    // Eliminate the impossible scenario of zero address sending this transaction
    require e.msg.sender != zeroAddress;
    calldataarg args;
    // verifying with all non-view functions
    f(e, args);

    // zero address should have the same balance, hence we found no way of claiming to zero address
    assert RewardToken.balanceOf(zeroAddress) == zeroAddressBalance;
}

// There should be no way to steal reward tokens from someone else (excluding OnBehalf functions)
rule cannotStealRewards(method f) filtered { 
        f -> !f.isView &&
        f.selector != sig:claimRewardsOnBehalf(address[] calldata, uint256, address, address, address).selector &&
        f.selector != sig:claimAllRewardsOnBehalf(address[] calldata, address, address).selector
    } {
    
    env e;
    address[] assets;
    requireSingleAddressInList(assets, AToken);
    // mark reward token balance of user
    uint256 userBalanceBefore = RewardToken.balanceOf(e.msg.sender);
    // mark rewards of user
    uint256 userRewards = getUserRewards(e, assets, e.msg.sender, RewardToken);
    require e.msg.sender != TransferStrategy;

    // Limit to single asset and single reward
    requireSingleAddressInList(getAssetsList(), AToken);
    requireSingleRewardForAsset(AToken, RewardToken);

    calldataarg args;
    // verifying with all non-view functions
    f(e, args);

    // mark reward token balance of user after transaction
    uint256 userBalanceAfter = RewardToken.balanceOf(e.msg.sender);
    // if user reward token balance increased, they must have been eligible for the amount
    assert userBalanceAfter > userBalanceBefore => userRewards >= assert_uint256(userBalanceAfter - userBalanceBefore);
}

// The handleAction function can only be called by the asset contract to update user data
rule handleActionModifiesCallingAssetUserState {
    address user;
    address reward;
    // Limit to single asset and single reward
    requireSingleAddressInList(getAssetsList(), AToken);
    requireSingleRewardForAsset(AToken, RewardToken);

    uint256 before = getUserAccruedRewards(user, reward);

    uint256 totalSupply;
    uint256 userBalance;
    env e;
    handleAction(e, user, totalSupply, userBalance);

    uint256 after = getUserAccruedRewards(user, reward);

    // if a user accrued rewards are changed by handleAction, it must have been done by the asset contract
    assert after != before => e.msg.sender == AToken;
}

//////////////////////////////////////////////
// The following section of rules all verify the same or similar property:
//  - claiming reduces accrued reward balance, and
//  - increases the reward token balance of the receiver
//
// This started out as a simple parameterized rule but had to be split out because of:
//  - requiring parameter access to the claim functions
//  - timeouts ... only the most reduced, single assert is not timing out ...
//////////////////////////////////////////////

    // Claiming the rewards with claimRewards() correctly reduces amount of accrued rewards of the user
    //  - with amount less than or equal to accrued rewards
    rule claimRewardsSendsRewards_assertRewards() {
        
        env e;
        address targetUser;
        uint256 amount;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 senderRewardBefore = getUserRewards(e, assets, e.msg.sender, RewardToken);
        require targetUser != TransferStrategy;
        // scenario when amount is less or equal to accrued user rewards
        require amount <= senderRewardBefore;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimRewards(e, assets, amount, targetUser, RewardToken);
        uint256 senderRewardAfter = getUserRewards(e, assets, e.msg.sender, RewardToken);

        // Sender rewards should decrese by the provided amount
        assert require_uint256(senderRewardAfter + amount) == senderRewardBefore;
    }

    // Claiming the rewards with claimRewards() sends correct amount of reward tokens to receiver
    //  - with amount less than or equal to accrued rewards
    rule claimRewardsSendsRewards_assertBalance() {
        
        env e;
        address targetUser;
        uint256 amount;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 targetUserRewardBalanceBefore = RewardToken.balanceOf(targetUser);
        uint256 senderRewardBefore = getUserRewards(e, assets, e.msg.sender, RewardToken);
        require targetUser != TransferStrategy;
        // scenario when amount is less or equal to accrued user rewards
        require amount <= senderRewardBefore;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimRewards(e, assets, amount, targetUser, RewardToken);
        uint256 targetUserRewardBalanceAfter = RewardToken.balanceOf(targetUser);

        assert require_uint256(targetUserRewardBalanceBefore + amount) == targetUserRewardBalanceAfter;
    }

    // Claiming the rewards with claimRewards() correctly reduces amount of accrued rewards of the user
    //  - with amount more than accrued rewards
    rule claimRewardsSendsRewards_assertRewards_bigAmount() {
        
        env e;
        address targetUser;
        uint256 amount;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 senderRewardBefore = getUserRewards(e, assets, e.msg.sender, RewardToken);
        require targetUser != TransferStrategy;
        // scenario when amount is more than accrued user rewards
        require amount > senderRewardBefore;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimRewards(e, assets, amount, targetUser, RewardToken);
        uint256 senderRewardAfter = getUserRewards(e, assets, e.msg.sender, RewardToken);

        // Sender rewards should be depleted
        assert senderRewardAfter == 0;
    }

    // Claiming the rewards with claimRewards() sends correct amount of reward tokens to receiver
    //  - with amount more than accrued rewards
    rule claimRewardsSendsRewards_assertBalance_bigAmount() {
        
        env e;
        address targetUser;
        uint256 amount;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 targetUserRewardBalanceBefore = RewardToken.balanceOf(targetUser);
        uint256 senderRewardBefore = getUserRewards(e, assets, e.msg.sender, RewardToken);
        require targetUser != TransferStrategy;
        // scenario when amount is more than to accrued user rewards
        require amount > senderRewardBefore;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimRewards(e, assets, amount, targetUser, RewardToken);
        uint256 targetUserRewardBalanceAfter = RewardToken.balanceOf(targetUser);

        // Balance should be increased by the amount of available/accrued rewards
        assert require_uint256(targetUserRewardBalanceBefore + senderRewardBefore) == targetUserRewardBalanceAfter;
    }

    // Claiming the rewards with claimRewardsToSelf() correctly reduces amount of accrued rewards of the user
    //  - with amount less than or equal to accrued rewards
    rule claimRewardsToSelfSendsRewards_assertRewards() {
        
        env e;
        uint256 amount;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 senderRewardBefore = getUserRewards(e, assets, e.msg.sender, RewardToken);
        require e.msg.sender != TransferStrategy;
        // scenario when amount is less or equal to accrued user rewards
        require amount <= senderRewardBefore;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimRewardsToSelf(e, assets, amount, RewardToken);
        uint256 senderRewardAfter = getUserRewards(e, assets, e.msg.sender, RewardToken);

        // Sender rewards should decrese by the provided amount
        assert require_uint256(senderRewardAfter + amount) == senderRewardBefore;
    }

    // Claiming the rewards with claimRewardsToSelf() sends correct amount of reward tokens to receiver
    //  - with amount less than or equal to accrued rewards
    rule claimRewardsToSelfSendsRewards_assertBalance() {
        
        env e;
        uint256 amount;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 targetUserRewardBalanceBefore = RewardToken.balanceOf(e.msg.sender);
        uint256 senderRewardBefore = getUserRewards(e, assets, e.msg.sender, RewardToken);
        require e.msg.sender != TransferStrategy;
        // scenario when amount is less or equal to accrued user rewards
        require amount <= senderRewardBefore;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimRewardsToSelf(e, assets, amount, RewardToken);
        uint256 targetUserRewardBalanceAfter = RewardToken.balanceOf(e.msg.sender);

        assert require_uint256(targetUserRewardBalanceBefore + amount) == targetUserRewardBalanceAfter;
    }

    // Claiming the rewards with claimRewardsToSelf() correctly reduces amount of accrued rewards of the user
    //  - with amount more than accrued rewards
    rule claimRewardsToSelfSendsRewards_assertRewards_bigAmount() {
        
        env e;
        uint256 amount;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 senderRewardBefore = getUserRewards(e, assets, e.msg.sender, RewardToken);
        require e.msg.sender != TransferStrategy;
        // scenario when amount is more than accrued user rewards
        require amount > senderRewardBefore;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimRewardsToSelf(e, assets, amount, RewardToken);
        uint256 senderRewardAfter = getUserRewards(e, assets, e.msg.sender, RewardToken);

        // Sender rewards should be depleted
        assert senderRewardAfter == 0;
    }

    // Claiming the rewards with claimRewardsToSelf() sends correct amount of reward tokens to receiver
    //  - with amount more than accrued rewards
    rule claimRewardsToSelfSendsRewards_assertBalance_bigAmount() {
        
        env e;
        uint256 amount;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 targetUserRewardBalanceBefore = RewardToken.balanceOf(e.msg.sender);
        uint256 senderRewardBefore = getUserRewards(e, assets, e.msg.sender, RewardToken);
        require e.msg.sender != TransferStrategy;
        // scenario when amount is more than to accrued user rewards
        require amount > senderRewardBefore;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimRewardsToSelf(e, assets, amount, RewardToken);
        uint256 targetUserRewardBalanceAfter = RewardToken.balanceOf(e.msg.sender);

        // Balance should be increased by the amount of available/accrued rewards
        assert require_uint256(targetUserRewardBalanceBefore + senderRewardBefore) == targetUserRewardBalanceAfter;
    }

    // Claiming the rewards with claimRewardsOnBehalf() correctly reduces amount of accrued rewards of the user
    //  - with amount less than or equal to accrued rewards
    rule claimRewardsOnBehalfSendsRewards_assertRewards() {
        
        env e;
        address user;
        address targetUser;
        uint256 amount;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 senderRewardBefore = getUserRewards(e, assets, user, RewardToken);
        require targetUser != TransferStrategy;
        // scenario when amount is less or equal to accrued user rewards
        require amount <= senderRewardBefore;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimRewardsOnBehalf(e, assets, amount, user, targetUser, RewardToken);
        uint256 senderRewardAfter = getUserRewards(e, assets, user, RewardToken);

        // Sender rewards should decrese by the provided amount
        assert require_uint256(senderRewardAfter + amount) == senderRewardBefore;
    }

    // Claiming the rewards with claimRewardsOnBehalf() sends correct amount of reward tokens to receiver
    //  - with amount less than or equal to accrued rewards
    rule claimRewardsOnBehalfSendsRewards_assertBalance() {
        
        env e;
        address user;
        address targetUser;
        uint256 amount;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 targetUserRewardBalanceBefore = RewardToken.balanceOf(targetUser);
        uint256 senderRewardBefore = getUserRewards(e, assets, user, RewardToken);
        require targetUser != TransferStrategy;
        // scenario when amount is less or equal to accrued user rewards
        require amount <= senderRewardBefore;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimRewardsOnBehalf(e, assets, amount, user, targetUser, RewardToken);
        uint256 targetUserRewardBalanceAfter = RewardToken.balanceOf(targetUser);

        assert require_uint256(targetUserRewardBalanceBefore + amount) == targetUserRewardBalanceAfter;
    }

    // Claiming the rewards with claimRewardsOnBehalf() sends correct amount of reward tokens to receiver
    //  - with amount more than accrued rewards
    rule claimRewardsOnBehalfSendsRewards_assertBalance_bigAmount() {
        
        env e;
        address user;
        address targetUser;
        uint256 amount;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 targetUserRewardBalanceBefore = RewardToken.balanceOf(targetUser);
        uint256 senderRewardBefore = getUserRewards(e, assets, user, RewardToken);
        require targetUser != TransferStrategy;
        // scenario when amount is more than to accrued user rewards
        require amount > senderRewardBefore;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimRewardsOnBehalf(e, assets, amount, user, targetUser, RewardToken);
        uint256 targetUserRewardBalanceAfter = RewardToken.balanceOf(targetUser);

        // Balance should be increased by the amount of available/accrued rewards
        assert require_uint256(targetUserRewardBalanceBefore + senderRewardBefore) == targetUserRewardBalanceAfter;
    }

    // Claiming the rewards with claimAllRewards() correctly reduces amount of accrued rewards of the user
    rule claimAllRewardsSendsRewards_assertRewards() {
        
        env e;
        address targetUser;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        require targetUser != TransferStrategy;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimAllRewards(e, assets, targetUser);
        uint256 senderRewardAfter = getUserRewards(e, assets, e.msg.sender, RewardToken);

        // Sender rewards should be depleted
        assert senderRewardAfter == 0;
    }

    // Claiming the rewards with claimAllRewards() sends correct amount of reward tokens to receiver
    rule claimAllRewardsSendsRewards_assertBalance() {
        
        env e;
        address targetUser;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 targetUserRewardBalanceBefore = RewardToken.balanceOf(targetUser);
        uint256 senderRewardBefore = getUserRewards(e, assets, e.msg.sender, RewardToken);
        require targetUser != TransferStrategy;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimAllRewards(e, assets, targetUser);
        uint256 targetUserRewardBalanceAfter = RewardToken.balanceOf(targetUser);

        assert require_uint256(targetUserRewardBalanceBefore + senderRewardBefore) == targetUserRewardBalanceAfter;
    }

    // Claiming the rewards with claimAllRewardsToSelf() correctly reduces amount of accrued rewards of the user
    rule claimAllRewardsToSelfSendsRewards_assertRewards() {
        
        env e;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        require e.msg.sender != TransferStrategy;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimAllRewardsToSelf(e, assets);
        uint256 senderRewardAfter = getUserRewards(e, assets, e.msg.sender, RewardToken);

        // Sender rewards should be depleted
        assert senderRewardAfter == 0;
    }

    // Claiming the rewards with claimAllToSelfRewards() sends correct amount of reward tokens to receiver
    rule claimAllRewardsToSelfSendsRewards_assertBalance() {
        
        env e;
        address[] assets;
        requireSingleAddressInList(assets, AToken);
        uint256 targetUserRewardBalanceBefore = RewardToken.balanceOf(e.msg.sender);
        uint256 senderRewardBefore = getUserRewards(e, assets, e.msg.sender, RewardToken);
        require e.msg.sender != TransferStrategy;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimAllRewardsToSelf(e, assets);
        uint256 targetUserRewardBalanceAfter = RewardToken.balanceOf(e.msg.sender);

        assert require_uint256(targetUserRewardBalanceBefore + senderRewardBefore) == targetUserRewardBalanceAfter;
    }

    // Claiming the rewards with claimAllRewardsOnBehalf() correctly reduces amount of accrued rewards of the user
    rule claimAllRewardsOnBehalfSendsRewards_assertRewards() {
        
        env e;
        address[] assets;
        address user;
        address targetUser;
        requireSingleAddressInList(assets, AToken);
        require targetUser != TransferStrategy;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimAllRewardsOnBehalf(e, assets, user, targetUser);
        uint256 senderRewardAfter = getUserRewards(e, assets, user, RewardToken);

        // Sender rewards should be depleted
        assert senderRewardAfter == 0;
    }

    // Claiming the rewards with claimAllRewardsOnBehalf() sends correct amount of reward tokens to receiver
    rule claimAllRewardsOnBehalfSendsRewards_assertBalance() {
        
        env e;
        address[] assets;
        address user;
        address targetUser;
        requireSingleAddressInList(assets, AToken);
        uint256 targetUserRewardBalanceBefore = RewardToken.balanceOf(targetUser);
        uint256 senderRewardBefore = getUserRewards(e, assets, user, RewardToken);
        require targetUser != TransferStrategy;

        // Limit to single asset and single reward
        requireSingleAddressInList(getAssetsList(), AToken);
        requireSingleRewardForAsset(AToken, RewardToken);

        claimAllRewardsOnBehalf(e, assets, user, targetUser);
        uint256 targetUserRewardBalanceAfter = RewardToken.balanceOf(targetUser);

        assert require_uint256(targetUserRewardBalanceBefore + senderRewardBefore) == targetUserRewardBalanceAfter;
    }

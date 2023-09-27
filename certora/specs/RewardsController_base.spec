import "methods/Methods_base.spec";

///////////////// Properties ///////////////////////

    // Property: Reward index monotonically increase
    rule index_keeps_growing(address asset, address reward, method f) filtered { f -> !f.isView } {
        uint256 _index = getAssetRewardIndex(asset, reward);

        env e; calldataarg args;
        f(e, args);

        uint256 index_ = getAssetRewardIndex(asset, reward);
        
        assert index_ >= _index;
    }

    // Property: User index cannot surpass reward index
    invariant user_index_LEQ_index(address asset, address reward, address user)
        getUserAssetIndex(user, asset, reward) <= getAssetRewardIndex(asset, reward);


    // check this rule for every change in setup to make sure all is reachable 
    // use builtin rule sanity;

    //  Property: claiming reward twice is equivalent to one claim reward 
    //  Note : this rule is implemented by comparing the whole storage 
    rule noDoubleClaim() {

        env e; 
        //arbitrary array of any length (might be constrained due to loop unrolling )
        address[] assets; 
        uint256 l = assets.length;
        address to;
        claimAllRewards(e, assets, to);
        storage afterFirst = lastStorage;
        claimAllRewards(e, assets, to);
        storage afterSecond = lastStorage;

        assert afterSecond == afterFirst;
    }

    // Property: only an authorized user or the user itself can cause a reduction in accrued rewards for this user
    rule onlyAuthorizeCanDecrease(method f) filtered { f -> !f.isView } {

        address user; address reward;
        uint256 before = getUserAccruedRewards(user, reward);

        env e;
        calldataarg args;
        f(e,args);

        uint256 after = getUserAccruedRewards(user, reward);

        assert after < before => (getClaimer(user) == e.msg.sender || user == e.msg.sender);
    }



import "./ERC20_methods.spec";

using DummyERC20_AToken as AToken;
using DummyERC20_rewardToken as RewardToken;
using TransferStrategyHarness as TransferStrategy;

/////////////////// Methods ////////////////////////

    methods {
        // 
        function getAssetRewardIndex(address, address) external returns (uint256) envfree;
        function getRewardsData(address, address) external returns (uint256, uint256, uint256, uint256) envfree;
        function getUserAssetIndex(address, address, address) external returns (uint256) envfree;

        function isRewardEnabled(address) external returns (bool) envfree;
        function EMISSION_MANAGER() external returns (address) envfree;
        function getTransferStrategy(address) external returns (address) envfree;
        function getRewardOracle(address) external returns (address) envfree;
        function getRewardsByAsset(address asset) external returns (address[] memory) envfree;
        function getLastUpdateTimestamp(address asset, address reward) external returns (uint256) envfree;
        function getRewardsList() external returns (address[] memory) envfree;
        function getAvailableRewardsCountByAsset(address) external returns (uint256) envfree;
        function getAssetsList() external returns (address[] memory) envfree;
        function getAssetScaledTotalSupply(address) external returns (uint256) envfree;
        function getUserDataByAssetByReward(address user, address asset, address reward) external returns (uint256, uint256) envfree;
        function getUserRewards(address[] calldata, address, address) external returns (uint256);

        function claimAllRewards(address[] calldata, address) external returns (address[] memory, uint256[] memory);
        function claimRewards(address[] calldata, uint256, address, address) external  returns (uint256);
        function claimRewardsOnBehalf(address[] calldata, uint256, address, address, address) external returns (uint256);
        function claimRewardsToSelf(address[] calldata, uint256, address) external returns (uint256);
        function claimAllRewardsToSelf(address[] calldata) external returns (address[] memory, uint256[] memory);
        function claimAllRewardsOnBehalf(address[] calldata, address, address) external returns (address[] memory, uint256[] memory);
        
        // AToken functions
        function _.getScaledUserBalanceAndSupply(address) external => DISPATCHER(true);
        function _.scaledTotalSupply() external => DISPATCHER(true);
        function _.handleAction(address, uint256, uint256) external => DISPATCHER(true);

        // TransferStrategyBase functions
        function _.performTransfer(address, address, uint256) external => DISPATCHER(true);

        // RewardToken functions
        function RewardToken.balanceOf(address) external returns (uint256) envfree;

        // Oracle - assume any value 
        function _.latestAnswer() external => NONDET;

        //envfree functions
        function getUserAccruedRewards(address, address ) external returns(uint256) envfree; 
        function getClaimer(address) external returns (address) envfree;
    }

///////////////// DEFINITIONS //////////////////////

    // Returns true if f is one of the claims functions; false otherwise
    definition isClaimFunction(method f) returns bool = (
        f.selector == sig:claimAllRewards(address[] calldata, address).selector ||
        f.selector == sig:claimAllRewardsOnBehalf(address[] calldata, address, address).selector ||
        f.selector == sig:claimAllRewardsToSelf(address[] calldata).selector ||
        f.selector == sig:claimRewards(address[] calldata, uint256, address, address).selector ||
        f.selector == sig:claimRewardsOnBehalf(address[] calldata, uint256, address, address, address).selector ||
        f.selector == sig:claimRewardsToSelf(address[] calldata, uint256, address).selector
    );

////////////////// FUNCTIONS //////////////////////

    // Function to require the reward to be active. There's several elements in RewardData struct that need to be valid for this:
    //  - emissionPerSecond must be positive otherwise no rewards are accruing
    //  - distributionEnd must be in the future otherwise distribution has already ended
    //  - lastUpdateTimestamp must be equal or less than current timestamp (sanity property, covered by invariant)
    function requireActiveReward(address asset, address reward, env e) {
        uint256 emissionPerSecond;
        uint256 distributionEnd;
        _, emissionPerSecond, _, distributionEnd = getRewardsData(asset, reward);

        // require some emission of rewards
        require emissionPerSecond > 0;
        // distribution must not have ended
        require distributionEnd > e.block.timestamp;
        // require lastUpdateTimestamp to be less than or equal to current timestamp, 
        // property ensured by lastUpdateLessOrEqualToCurrentTimestamp invariant
        requireInvariant lastUpdateLessOrEqualToCurrentTimestamp(e, asset, reward);
    }

    // Function to require and set a single asset
    function requireSingleAsset(address asset) {
        address[] assetsList = getAssetsList();
        require assetsList.length == 1;
        require assetsList[0] == asset;
    }

    function requireSingleAddressInList(address[] assetList, address asset) {
        require assetList.length == 1;
        require assetList[0] == asset;
    }

    // Function to require and set a single reward for a given asset
    function requireSingleRewardForAsset(address asset, address reward) {
        address[] rewards = getRewardsByAsset(asset);
        address[] rewardsList = getRewardsList();
        require rewards.length == 1;
        require rewards[0] == reward;
        require rewardsList.length == 1;
        require rewardsList[0] == reward;
        require getAvailableRewardsCountByAsset(asset) == 1;
    }
    




## Certora Verification Setup

### Conf files:

1. use default.conf as a starting point. It is a simpler configuration and should be used to make sure the rule is proven first on a simplified version of the code.

2. verifyRewardsController_verified.conf should be used to check for better coverage. it contains more loop unrolling

3. verifyRewardsController_multiReward_verified.conf should be used  to check for multi-rewards. it contains more erc20 and multi-reward transferStrategy harness.

If you're using solc-select, you can delete the solc8.10 and just leave "" there. 


### Harness files:

1. TransferStrategy: There are three harness files viz. TransferStrategyHarness, TransferStrategyMultiRewardHarness and TransferStrategyMultiRewardHarnessWithLinks. The first file is meant for simulating a single reward token and is linked to one dummy ERC20 contract. The second file is meant to simulate multiple rewards without any links. The third file is linked to two specific dummy ERC20 contract and hence could be more performant than the second. For working on multi-reward, try using the second file without any links and if you run into timeouts, you can try with third one with links.

2. Tokens: There are two files here to handle any ERC20 function calls and a mock AToken contract to handle calls to AToken.

3. RewardControllerHarness: This is the harness file for the contract being verified. This is where you'll do most of your harnessing work.
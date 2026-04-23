# Formalizing Markov Decision Processes in Lean

[![Blueprint](https://img.shields.io/badge/Blueprint-WIP-blue)](https://formalproofs.github.io/MDPLib)

Verified Lean algorithms for solving tabular MDPs and proving their properties. The focus of this project is on two main goals:

1. Basic algorithms that can solve robust and risk-averse MDPs of moderate size. 

2. Proofs of correctness of algorithms and fundamental MDP properties which can be used independently to prove structural results, such as the optimality of certain policy class.


## Status

### General

- [ ] Left and right continuity (exists?)
- [ ] Generalized inverse; left and right continous functions (exists?)

### Basic probability properties

- [x] Definitions: probability space and definition
- [x] Definitions: probability, expectation, conditional properties
- [x] Tower property, law of the unconscious statistician
- [x] Quantile definition and basic properties
- [ ] Quantile under monotone transformation
- [ ] Conditional probability = change of measure
- [ ] Independent random variables
- [x] Construct probability from a compile-time input
- [ ] Construct probability from runtime input

### Value at Risk

- [x] Definition (non-constructive)
- [x] Practical implementation O(n^2) and correctness
- [ ] Fast practical implementation O(n log n) and correctness
- [ ] Definition of VaR as minimization 
- [x] VaR is positively homogeneous and monotone
- [ ] VaR is translation (cash) invariant 
- [ ] VaR under monotone transformation
- [ ] Check risk measure values in a JSON file

### MDP: Basics

- [x] Definition of MDP 
- [x] Definition of policies (history, Markov, stationary)
- [ ] Policy induces a distribution over histories
- [ ] Definition of value function (history-dependent)


### Finite Horizon

- [x] Histories and manipulation
- [ ] Probability space over histories
- [ ] Return and optimal return using histories
- [ ] History-dependent value function and dynamic program
- [ ] Markov optimal value function and optimal policy 
- [ ] DP algorithms

### Risk-averse finite horizon

- [ ] History-dependent utility functions
- [ ] Augmented value function dynamic program 
- [ ] VaR computation from utility function
- [ ] VaR DP decomposition as in Hau et al., 2023

### Discounted infinite horizon


### Average reward horizon




## Lean Resources


### Most useful

* Overview of tactics: <https://github.com/madvorak/lean4-tactics>
* Comprehensive list of tactics: <https://seasawher.github.io/mathlib4-help/tactics/>
* Loogle: <https://loogle.lean-lang.org/>
* Moogle: <https://www.moogle.ai/> 

### Others

* Blueprint: <https://github.com/PatrickMassot/leanblueprint>
* Lean packages and extensions: <https://reservoir.lean-lang.org/>
* Notations: <https://github.com/leanprover-community/lean4-mode/blob/master/data/abbreviations.json>
* Resource for Probability: <https://korivernon.com/documents/MathematicalStatisticsandDataAnalysis3ed.pdf>




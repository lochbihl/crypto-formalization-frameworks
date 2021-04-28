Comparing frameworks for mechanizing crypto-formalization-frameworks
====================================================================

This repository provides an overview over frameworks for mechanizing cryptographic proofs in a proof assistant.
It collects the ideas and design decisions behind those frameworks, and small cryptographic examples that distill the fundamental formalization challenges.
This allows us to better compare the frameworks and understand the impact of modelling approaches.
Formalizations of the examples are merely linked to rather than being included in this repository such that they can be easily evolved with the framework.

The following frameworks are currently covered (listed in alphabetical order):

Framework | Proof assistant
--------- | ---------------
[CryptHOL](https://www.isa-afp.org/entries/CryptHOL.html) | Isabelle/HOL
[FCF](https://github.com/adampetcher/fcf) | Coq
[IPDL](https://github.com/ipdl/ipdl) | Coq
[SSProve](https://github.com/SSProve) | Coq


## Formalization Challenges

This section collects conceptual challenges that frameworks for formalizing cryptographic proofs must solve.

### Computational assumptions

Shallow embeddings use the function space of the underlying logic, which does not have a computational interpretation.
It is therefore difficult to formally capture computational costs inside the logic.
This prevents quantifying over all computationally bounded adversaries in computational assumptions.

### State encapsulation

Games are stateful as later interactions with an adversary may depend on earlier ones.
Yet the adversary must not access certain parts of this state.
Otherwise there would be no hidden randomness and the adversary could trivially win the cryptographic game.
In a shallow embedding, the unknown adversary is not constrained by any program syntax or computational model.
So it is, e.g., unsound to formalize a distinguisher as a function that is given the setting it should interact with as a parameter.
Rather, the internal state of the setting must be formally encapsulated.

Encapsulation can also simplify composition of several arguments as components with disjoint state are probabilistically independent.


### Scheduling model

Simple cryptographic games prescribe a fixed interaction pattern between the game and the adversary or distinguisher.
With composable security notions, the adversary schedules the interaction pattern with the game.
Frameworks suitable for one model are not necessarily easy-to-use for the other.


## Framework Overview

### CryptHOL

CryptHOL models cryptographic games shallowly in the proof assistant Isabelle/HOL with the following semantic domains:

Concept | Semantic domain
------- | ---------------
Pure computations | Function space
Probabilistic computations | Subprobability distributions
Interactive computations | Probabilistic input-output transition systems as a coalgebraic datatype

Cryptographic games and algorithms are defined using the definition facilities of the Isabelle/HOL proof assistant using a monadic syntax.
One cannot reason about the syntactic definition due to the shallow embedding,
but proof automation can look at the term structure and exploit it in the proof search.

Interaction between the game and an adversary can be modelled in two ways:

1. For games with a fixed interaction pattern,
   the adversary is represented an interactive computation that the game invokes.
   The game threads through the adversary's state across invocations.
   Security is defined flexibly in terms of some winning condition.

2. When the adversary controls the interaction pattern,
   it typically acts as a distinguisher between two settings.
   Each setting is given by some oracles that the adversary can query.
   Security is defined via the distinguishing advantage between the two settings.

Security proofs are composed with steps from the following categories:

* Relational reasoning using a bisimulation-style proof rules
* Equational reasoning using identities provable in the semantic domains, e.g., reordering of sampling, resampling
* Applying cryptographic assumptions or failure lemmas
* Trace equivalence reasoning when the adversary controls the interaction pattern, e.g., for switching from lazy to eager sampling.


**Resources:**
* [Source code](https://www.isa-afp.org/entries/CryptHOL.html)
* [Tutorial](https://eprint.iacr.org/2018/941)
* [Theory paper](https://eprint.iacr.org/2017/753)
* [MPC](https://arxiv.org/abs/1805.12482)
* [Sigma and commitment protocols](https://eprint.iacr.org/2019/1185)
* [Constructive Cryptography formalization](http://andreas-lochbihler.de/pub/lochbihler2019csf.pdf)
* [Abstracting over system communication patterns](http://andreas-lochbihler.de/pub/basin2021.pdf)


### FCF

**Resources:**
* [Source code](https://github.com/adampetcher/fcf)
* [Paper](https://arxiv.org/abs/1410.3735)


### IPDL

IPDL shallowly embeds a process calculus into Coq with the following syntax:
```
r ::= 
   | Read c // where c is a channel
   | Samp D // where D is a probability distribution
   | x <- r in r // monadic bind
   | return e
   
P ::=
   | c ::= r // channel c is bound to reaction r
   | P || P // parallel composition
   | new c : \tau in P // private channel creation
   | 0
```

Above, `r` stands for a _reaction_, which defines the behavior of channels. 
Channels are write-once, and only one reaction can be bound to a channel.
(Repeated queries / state access are encoded using vectors of channels of some parameterized size.)
Private channels capture state encapsulation. Interaction between processes `P` and the outside envrionment/adversary is
done by using free channels (i.e., channels not created by `new`).
The point of IPDL is that channels have very simple behaviors (governed by reactions). In this way, IPDL can also 
be thought of as **interactive probabilistic circuits**. While the syntax of IPDL does not allow control flow, public, static control flow can be encoded 
through metaprogramming in Coq.

#### Reasoning in IPDL

Because the behaviors of channels in IPDL are simple and captured by the syntax, IPDL admits an equational reasoning framework. The main judgement 
in IPDL is `P ~=_delta Q` (`P` is `delta` distance away from `Q`). (The Coq framework does not yet reason about the `delta`.) 

There are rules for:
* basic properties of `||` and `new`, including congruence rules for `~=` wrt `||` and `new`;
* soundly inlining channels into other channels; and
* reasoning equationally about probability distributions inside of reactions.


**Resources:**
* [Source code](https://github.com/ipdl/ipdl)
* [Paper](https://eprint.iacr.org/2021/147)


### SSProve

**Resources:**
* [Source code](https://github.com/SSProve)
* [Paper](https://eprint.iacr.org/2021/397)


### Related formalizations

Related to the above are the following works:

* [EasyUC](https://github.com/easyuc/EasyUC)
  formalizes parts of the UC framework in EasyCrypt.




## Formalization examples

### Fixed interaction patterns

#### One-time pad

#### Multi-party computation GMW

* [CryptHOL](https://www.isa-afp.org/browser_info/current/AFP/Multi_Party_Computation/GMW.html)


### Scheduler-based examples

Scheduler-based examples typically follow the ideal-real world paradigm and define security using a simulator.

#### One-time pad

* CryptHOL
  * [with a pre-shared key](https://www.isa-afp.org/browser_info/current/AFP/Constructive_Cryptography/One_Time_Pad.html)
  * [composable version](https://www.isa-afp.org/browser_info/current/AFP/Constructive_Cryptography_CM/One_Time_Pad.html)


#### KEM-DEM


#### Diffie-Hellman key exchange

* [CryptHOL](https://www.isa-afp.org/browser_info/current/AFP/Constructive_Cryptography_CM/Diffie_Hellman_CC.html)


### Composition examples

#### Diffie-Hellman key exchange + One-time pad

* [CryptHOL](https://www.isa-afp.org/browser_info/current/AFP/Constructive_Cryptography_CM/DH_OTP.html)

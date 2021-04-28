
# DHKE in IPDL

Below, I am using syntax that is a bit different than the Coq implementation.
Processes are parameterized by channels, either _output_ or _input_. 
An output channel can be only output on once, but read as input elsewhere in the protocol.
The entire example only uses single channels, but more complex examples
can be done using vectors of channels as well.

In IPDL, there is no distinction yet between external channels meant for the environment, or backdoor channels for the adversary. (This distinction matters for the simulator, which only operates on backdoor channels.) We currently maintain this distinction by hand, but it would be easy to write a type system that takes care of this as well. 

### DDH assumption:

    DDH0[out o : group * group * group] :=
        new x, y : Z_q in
            x := uniform Z_q 
            y := uniform Z_q
            o := (g^x, g^y, g^(x*y))

    ~=

    DDH1[out o : group * group * group] :=
        new x, y : Z_q in
            x := uniform Z_q 
            y := uniform Z_q
            o := (g^x, g^y, g^(x*y))

Notes on above: there is only one form of composition -- the `||` operator -- thus, there is no particular order between the channels `x` and `y`. If a value of a channel appears in a reaction,
then I am doing an implicit read; e.g., the reaction `(g^x, g^y, g^(x * y))` is shorthand for
`(a <- Read x in b <- Read y in return (g^a, g^b, g^(a*b))`.

### Forwarder protocols

The `FAuth` functionality models a forwarder of a single message. It takes as input a message `m` from the environment, and outputs it to the adversary on the `leak` channel; concurrently, it outputs to the environment along `o` only when the `ok` channel from the adversary is enabled. Note there is _no_ sequentiality assumption between the `leak` and the `ok` channels, since they are both used by the adversary.

    FAuth[in m : group, out leak : group, in ok : unit, out o : group] :=
        leak := m
        out := let _ = ok in return m


The `FSec` functionality is similar, except that it does not leak a message. However, it does still leak the timing of the message `m`.

    FSec[in m : group, out leak : unit, in ok : unit, out o : group] :=
        leak := let _ = m in return ()
        out := let _ = ok in return m

    
### DHKE protocol

We specify the `DHKE` protocol by modularly specifying the two parties, which are symmetric in this case, and differ only in the channels they are given. 

    DHKEParty[out send : group, in recv : group, out o : group] :=
        new q : Z_q in
            q := uniform Z_q
            send := g^q
            o := recv^q

    DHKE[out leak1, leak2 : group, in ok1, ok2 : group, out oA, oB : group] :=
        new send1, send2, recv1, recv2 : group in
            DHKEParty[send1, recv2, oA] // Alice
            DHKEParty[send2, recv1, oB] // Bob
            FAuth[send1, leak1, ok1, recv1] // FAuth A -> B
            FAuth[send2, leak2, ok2, recv2] // FAuth B -> A


### DHKE Ideal

    KEIdeal[in schedA, schedB : unit, out oA, oB : group] :=
        new q : Z_q in
            q := uniform Z_q
            oA := let _ = schedA in g^q
            oB := let _ = schedB in g^q

### Simulation proof goal

To show that `DHKE` is secure, we need to show the existence of a simulator `Sim` which hooks up to the adversary interface in the ideal world, and exposes the adversary interface of the real world. Specifically, we have that `Sim[out schedA, schedB : unit, out leak1, leak2 : group, in ok1, ok2 : group]` is such that:

    DHKE[leak1, leak2, ok1, ok2, oA, oB] ~= 
    new schedA, schedB : unit. 
        Sim[out schedA, schedB : unit, out leak1, leak2 : group, in ok1, ok2 : group] ||
        KEIdeal[schedA, schedB, oA, oB]


## Proof

### Simplifying `DHKE`

We first simplify `DHKE`, and flatten the protocol structure to make it easy to reason about.


    DHKE1[out leak1, leak2 : group, in ok1, ok2 : group, out oA, oB : group] :=
        new send1, send2, recv1, recv2 : group, qA, qB : Z_q in
            // Alice
            qA := uniform Z_q
            send1 := g^qA
            oA := recv2^qA

            // Bob
            qB := uniform Z_q
            send2 := g^qB
            oB := recv1^qB

            // FAuth A -> B
            leak1 := send1
            recv1 := let _ = ok1 in send1

            // FAuth B -> A
            leak2 := send2
            recv2 := let _ = ok2 in send2


In the above, we can now _inline_ the `send` and `recv` channels, since they are locally generated and deterministic. After we inline the channels, we see they are unused, so we can remove them from the protocol. Since the `recv` channels depend on the `send` channels, we first eliminate the `send` channels, and then the `recv` channels.

    DHKE2[out leak1, leak2 : group, in ok1, ok2 : group, out oA, oB : group] :=
        new qA, qB : Z_q in
            // Alice
            qA := uniform Z_q
            oA := let _ = ok2 in (g^qB)^qA

            // Bob
            qB := uniform Z_q
            oB := let _ = ok1 in (g^qA)^qB

            // FAuth A -> B
            leak1 := g^qA

            // FAuth B -> A
            leak2 := g^qB

### Factoring into DDH

At this point, we show that `DHKE2` is equivalent to a protocol which makes use of `DDH0` to generate all group elements.

    DHKE3[out leak1, leak2 : group, in ok1, ok2 : group, out oA, oB : group] :=
        new ddh_samp : group * group * group in
            DDH0[ddh_samp]

            // Alice
            oA := let _ = ok2 in ddh_samp.2

            // Bob
            oB := let _ = ok1 in ddh_samp.2

            // FAuth A -> B
            leak1 := ddh_samp.0

            // FAuth B -> A
            leak2 := ddh_samp.1

The above rewrite is done by expanding `DDH0` and eliminating the channel `ddh_samp` appropriately.

Now, we replace `DDH0` by `DDH1` (which we can do since `||` is a congruence for approximate equivalence of protocols). After doing so, we may reduce and get:

    DHKE4[out leak1, leak2 : group, in ok1, ok2 : group, out oA, oB : group] :=
        new x, y, z : group in
            x := uniform Z_q
            y := uniform Z_q
            z := uniform Z_q

            // Alice
            oA := let _ = ok2 in g^z

            // Bob
            oB := let _ = ok1 in g^z

            // FAuth A -> B
            leak1 := g^x

            // FAuth B -> A
            leak2 := g^y

At this point, we see that `x` is a local probabilistic channel which is only used once (in `leak1`), and similarly for `y` and `leak2`. When local probabilistic channels are used linearly, we may inline them, obtaining the final simplification:

    DHKESimp[out leak1, leak2 : group, in ok1, ok2 : group, out oA, oB : group] :=
        new z : group in
            z := uniform Z_q

            // Alice
            oA := let _ = ok2 in g^z

            // Bob
            oB := let _ = ok1 in g^z

            // FAuth A -> B
            leak1 := let x = uniform Z_q in g^x

            // FAuth B -> A
            leak2 := let x = uniform Z_q in g^x

### Equivalence to `KEIdeal`

Let us recall the definition of `KEIdeal`:

    KEIdeal[in schedA, schedB : unit, out oA, oB : group] :=
        new q : Z_q in
            q := uniform Z_q
            oA := let _ = schedA in g^q
            oB := let _ = schedB in g^q


We now notice the only difference between `DHKESimp` and `KEIdeal` is the presence of the `leak` channels. Thus, we derive our simulator: it generates the `leak` channels at random, and passes information along accordingly.

    Sim[out schedA, schedB : unit, out leak1, leak2 : group, in ok1, ok2 : group] :=
        schedA := ok2
        schedB := ok1
        leak1 := let x = uniform Z_q in g^x
        leak2 := let x = uniform Z_q in g^x


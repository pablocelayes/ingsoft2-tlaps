-------------------- MODULE Euclides --------------------
EXTENDS Integers

p | q == \E d \in 1..q : q = p * d
Divisors(q) == {d \in 1..q : d | q}
Maximum(S) == CHOOSE x \in S : \A y \in S : x >= y 
GCD(p,q) == Maximum(Divisors(p) \cap Divisors(q))

CONSTANTS M, N
VARIABLES x, y

Init == (x = M) /\ (y = N)

Next == \/ /\ x < y
           /\ y' = y - x
           /\ x' = x
        \/ /\ y < x
           /\ x' = x-y
           /\ y' = y

Number == Nat \ {0}

InductiveInvariant == /\ x \in Number
                      /\ y \in Number
                      /\ GCD(x, y) = GCD(M, N)
                      
ASSUME NumberAssumption == M \in Number /\ N \in Number

THEOREM Pepe == Init => InductiveInvariant
    OBVIOUS
=======================================================
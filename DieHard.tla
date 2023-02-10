------------------------------ MODULE DieHard ------------------------------
(***************************************************************************)
(* This is the "jugs of water" problem from Die Hard 3.                    *)
(*                                                                         *)
(* See: https://www.youtube.com/watch?v=BVtQNK_ZUJg                        *)
(***************************************************************************)

(***************************************************************************)
(* Naturals gives us access to the range ".." operator.                    *)
(***************************************************************************)
EXTENDS Naturals

(***************************************************************************)
(* Our system state consists of the amount of water in each jug            *)
(***************************************************************************)
VARIABLES ThreeGal, FiveGal

(***************************************************************************)
(* TypeOK is a safety invariant that ensures our variables have the        *)
(* correct "types" (not really a thing in TLA+) and ranges.                *)
(*                                                                         *)
(* In this case, we are making sure that the jugs always have realistic    *)
(* amounts of water in them: empty up to their individual capacity.  This  *)
(* must be true for all states, thus an invariant we will model check.     *)
(***************************************************************************)
TypeOK == /\ ThreeGal \in (0..3)
          /\ FiveGal \in (0..5)

(***************************************************************************)
(* Init will define the initial state of our system.  The jugs begin       *)
(* empty!                                                                  *)
(***************************************************************************)
Init == /\ ThreeGal = 0
        /\ FiveGal = 0

(***************************************************************************)
(* Now to define the actions...  What can we do?                           *)
(*                                                                         *)
(* - Fill a jug from the faucet                                            *)
(*                                                                         *)
(* - Empty a jug                                                           *)
(*                                                                         *)
(* - Dump the contents of one into the other                               *)
(*                                                                         *)
(* Below are the temporal formulas for those...                            *)
(*                                                                         *)
(* Note: All variables' next state must be defined, there's no implicit:   *)
(* "it stays the same if I don't change it" like there is with             *)
(* programming.  If we don't say it, the water in ThreeGal could change to *)
(* anything during a FillFive step since we would be saying a FillFive     *)
(* step is any step where FiveGal ends up w/ 5 in it.                      *)
(***************************************************************************)

FillFive == /\ FiveGal' = 5
            /\ UNCHANGED ThreeGal
FillThree == /\ ThreeGal' = 3
             /\ UNCHANGED FiveGal

EmptyFive == /\ FiveGal' = 0
             /\ UNCHANGED ThreeGal
EmptyThree == /\ ThreeGal' = 0
              /\ UNCHANGED FiveGal
              
ThreeToFive == \/ /\ FiveGal + ThreeGal \leq 5  \* It all fits
                  /\ ThreeGal' = 0
                  /\ FiveGal' = FiveGal + ThreeGal
               \/ /\ FiveGal + ThreeGal > 5  \* Fill rest of the way
                  /\ FiveGal' = 5
                  /\ ThreeGal' = FiveGal + ThreeGal - 5
FiveToThree == \/ /\ FiveGal + ThreeGal \leq 3  \* It all fits
                  /\ FiveGal' = 0
                  /\ ThreeGal' = FiveGal + ThreeGal
               \/ /\ FiveGal + ThreeGal > 3  \* Fill rest of the way
                  /\ ThreeGal' = 3
                  /\ FiveGal' = FiveGal + ThreeGal - 3

(***************************************************************************)
(* A "next state" step is one that takes any of our previously defined     *)
(* steps.                                                                  *)
(***************************************************************************)
Next == \/ FillFive
        \/ FillThree
        \/ EmptyFive
        \/ EmptyThree
        \/ FiveToThree
        \/ ThreeToFive

(***************************************************************************)
(* The overall spec is one where we start in the initial state, then       *)
(* always take a step according to the rules                               *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<FiveGal, ThreeGal>>

(***************************************************************************)
(* The bomb is defused when we get 4 gal into the jug                      *)
(***************************************************************************)
Defused == FiveGal = 4

=============================================================================
\* Modification History
\* Last modified Thu Feb 02 12:44:30 EST 2023 by jstrunk
\* Created Thu Feb 02 11:43:04 EST 2023 by jstrunk

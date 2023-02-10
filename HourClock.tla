----------------------------- MODULE HourClock ------------------------------
\* EXTENDS is like #include or import... brings in definitions for us to use
EXTENDS Naturals

\* Declare our state (variables)
VARIABLE hr

(***************************************************************************)
(* HCini is going to define the initial state(s) of the clock.             *)
(*                                                                         *)
(* - Our clock can start w/ its hand at any position                       *)
(*                                                                         *)
(* Reminder: This is not programming.  We are not saying to assign hr a    *)
(* value in the range of 1 to 12.  We are just saying that if hr happens   *)
(* to be in that range, the expression HCini evaluates to True, otherwise  *)
(* it evaluates to False.                                                  *)
(***************************************************************************)
HCini == hr \in (1 .. 12)

(***************************************************************************)
(* Below is a temporal formula: It has primed variables, so it describes a *)
(* transition of variable(s) between states.                               *)
(*                                                                         *)
(* HCnxt defines how we move between states.  I.e., If the clock is        *)
(* advancing during a system step, the expression HCnxt will be True.      *)
(* Think of this like HCini, above.  All kinds of state changes may be     *)
(* happening, but an HCnxt step is one that matches the expression below.  *)
(*                                                                         *)
(* Syntax note: IF, THEN is like the ternary "?:" operator from            *)
(* programming I've written out the long form below...                     *)
(***************************************************************************)

\* HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HCnxt == \/ /\ hr # 12
            /\ hr' = hr + 1
         \/ /\ hr = 12
            /\ hr' = 1

(***************************************************************************)
(* HC is the whole specification for our clock.                            *)
(*                                                                         *)
(* For the spec (HC) to be True, the initial state must conform to HCini   *)
(* and system steps must conform to HCnxt.                                 *)
(*                                                                         *)
(* The stuff around HCnxt: - [] aka "box" means "always".  i.e., must be   *)
(* true of all transitions - Subscript hr limits this to steps where hr    *)
(* changes.  So, if hr changes during a step, HCnxt must be True for that  *)
(* step.  If hr doesn't change, then HCnxt doesn't matter.                 *)
(***************************************************************************)

HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------

(***************************************************************************)
(* The right arrow is "implication": if LEFT is True, RIGHT is also True.  *)
(* If LEFT is False, it says NOTHING about RIGHT!                          *)
(*                                                                         *)
(* A B (A=>B)                                                              *)
(*                                                                         *)
(* F F T                                                                   *)
(*                                                                         *)
(* F T T                                                                   *)
(*                                                                         *)
(* T F F                                                                   *)
(*                                                                         *)
(* T T T                                                                   *)
(*                                                                         *)
(* We are asserting that the spec HC implies that HCini will always be     *)
(* True.  That is, for any system that conforms to the specification HC,   *)
(* HCini will evaluate to True in all of that system's states.             *)
(***************************************************************************)
THEOREM HC => []HCini

(***************************************************************************)
(* Liveness: The clock should "run"                                        *)
(*                                                                         *)
(* Sloppy, but illustrative: If the clock ever says it's 2 o'clock, it     *)
(* should eventually reach 7 o'clock.                                      *)
(*                                                                         *)
(* To express this, we need to say hr=2 "leads to" hr=7.  i.e, if we ever  *)
(* get to a state of 2, we will eventually, unavoidabally reach a state of *)
(* 7.                                                                      *)
(*                                                                         *)
(* Diamond <> means "eventually".  <>A means A will be True at some time   *)
(* in the future.                                                          *)
(*                                                                         *)
(* []<> means "always eventually".  "Leads to" A ~> B means [](A => <>B).  *)
(* If A is ever True, eventually B will be True.                           *)
(***************************************************************************)

Live == hr = 2 ~> hr = 7

(***************************************************************************)
(* Adding "weak fairness" to our spec: The spec FairHC is the same as the  *)
(* spec HC, but w/ weak fairness.                                          *)
(*                                                                         *)
(* Weak fairness means that if an action is continuously enabled (i.e.,    *)
(* possible), it will eventually happen.  We're basically saying that our  *)
(* clock must eventually advance.                                          *)
(***************************************************************************)
FairHC == HC /\ WF_hr(HCnxt)

=============================================================================
\* Modification History
\* Last modified Fri Feb 03 08:56:11 EST 2023 by jstrunk
\* Created Thu Feb 02 09:59:52 EST 2023 by jstrunk

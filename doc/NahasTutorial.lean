/-!
# Mike Nahas's Low-level Lean Tutorial

Started 2025-07-25
Tested with Lean 4.21.0

-----------------------------------

I wanted to learn Lean.
I decided to do that by translating all the proofs from my Coq tutorial into Lean.
Most of these were done by ChatGPT, but I did the hard ones myself
and edited some ChatGPT output to fit my ideas of style.

This file contains all those proofs.
It is NOT meant to be an Lean tutorial.
It is just a cheatsheet for me if I ever want to use Lean in the future.
I'm making the file available in case anyone who liked my Coq tutorial wanted to see what Lean was like.

-----------------------------------

Lean does not have a built-in documentation format, like Agda or Coq.

## Comments

You can comment until the end of line using: --

Multi-line comments are inside / - and - /  (without the spaces inbetween the characters.)

-/


/-
Lean allows unicode.  The → arrow is written in many editors with "\to".
-/

theorem myFirstProof : ∀ (A : Prop), A → A := by
  intros A
  intros proofOfA
  exact proofOfA


theorem myFirstProof__again : ∀ (A : Prop), A → A := by
  intros A
  intros proofOfA
  exact proofOfA


theorem myFirstProof__again__again : ∀ (A : Prop), A → A := by
  intros A
  intros proofOfA
  exact proofOfA


/- Lean uses the elegant "let ..." rather than Coq's awkward "pose (...)" -/
theorem forwardSmall : ∀ (A B : Prop), A → (A → B) → B := by
  intros A
  intros B
  intros proofOfA
  intros aImpliesB
  let proofOfB := aImpliesB proofOfA
  exact proofOfB

/- Lean has "refine".
  Holes are written with ?_.

  Unfortunately, indentation matters in Lean.
  I cannot indent when the goal changes after refine.
  I abuse the bullet · tactic, which says "try to solve just the first subgoal".
  I'm not a fan, but it is better than nothing.

  The bullet is typed in most editors with "\.".
-/
theorem backwardSmall : ∀ (A B : Prop), A → (A → B) → B := by
  intros A B
  intros proofOfA A_implies_B
  refine A_implies_B ?_  -- Cannot indent after changing goal!  Indent matters in Lean.
  · exact proofOfA


theorem backwardLarge : ∀ (A B C : Prop), A → (A → B) → (B → C) → C := by
  intros A B C
  intros proofOfA A_implies_B B_implies_C
  refine B_implies_C ?_
  · refine A_implies_B ?_
    · exact proofOfA

/- Again, indentation matters in Lean.
  This is best I can do, using the bullet tactic.
-/
theorem backwardHuge : ∀ (A B C : Prop), A → (A → B) → (A → B → C) → C := by
  intros A B C
  intros proofOfA A_implies_B A_imp_B_imp_C
  refine A_imp_B_imp_C ?_ ?_
  · exact proofOfA

  · refine A_implies_B ?_
    · exact proofOfA


theorem forwardHuge : ∀ (A B C : Prop), A → (A → B) → (A → B → C) → C := by
  intros A B C
  intros proofOfA A_implies_B A_imp_B_imp_C
  let proofOfB := A_implies_B proofOfA
  let proofOfC := A_imp_B_imp_C proofOfA proofOfB
  exact proofOfC


/-!
In Lean, the proof of True is "True.intro".

inductive Bool : Type
  | false : Bool
  | true  : Bool

inductive True : Prop
  | intro : True

inductive False : Prop
-/

theorem trueCanBeProven : True := by
  exact True.intro


theorem falseCannotBeProven : ¬ False := by
  unfold Not
  intros proofOfFalse
  exact proofOfFalse


theorem falseCannotBeProven__again : ¬ False := by
  intros proofOfFalse
  cases proofOfFalse


theorem thmTrueImpTrue : True → True := by
  intros proofOfTrue
  exact True.intro  -- "exact proofOfTrue" also works.


theorem thmFalseImpTrue : False → True := by
  intros proofOfFalse
  exact True.intro  -- "cases proofOfFalse" also works.


/- Lean uses "cases" instead of Coq's "case" -/

theorem thmFalseImpFalse : False → False := by
  intros proofOfFalse
  cases proofOfFalse  -- "exact proofOfFalse" also works but is not recommended.


theorem thmTrueImpFalse : ¬ (True → False) := by
  intros tImpliesF
  refine tImpliesF ?_
  · exact True.intro


/- Lean has "unfold". -/
theorem absurd2 : ∀ (A C : Prop), A → ¬ A → C := by
  intros A C
  intros proofOfA proofThatACannotBeProven
  unfold Not at proofThatACannotBeProven
  let proofOfFalse := proofThatACannotBeProven proofOfA
  cases proofOfFalse


/-!
inductive Bool : Type
  | false : Bool
  | true  : Bool
-/

/- Lean's libraries do not have these function.
   I added them.
-/
/- Putting @[simp] before a definition lets the "simp" tactic use it. -/

@[simp] def eqb (b1 b2 : Bool) : Bool :=
  match b1, b2 with
  | true,  true  => true
  | true,  false => false
  | false, true  => false
  | false, false => true

@[simp] def isTrue (b : Bool) : Prop :=
  match b with
  | true  => True
  | false => False


/- Lean's "simp" does more than Coq's "simpl".
  It uses a list of definitions to simplify a goal.
  It will also SOLVE the goal.

  I don't like that it solves the goal,
  because it is hard to show what is definitionally equal.
  AND it hides that the subgoal ended and a new one might start.

  If you see "simp" followed by a commented out exact,
  it is probably because it solved the goal that exact was meant to solve.
-/

theorem trueIsTrue : isTrue true := by
  simp
--  exact True.intro


theorem notEqbTrueFalse : ¬ isTrue (eqb true false) := by
  simp
--  exact falseCannotBeProvenAgain


/- You can indent cases when you use "cases ... with".
  After the "with" comes
  | constructor1 constructor_arg11 constructor_arg12 ... => ...
  | constructor2 constructor_arg21 constructor_arg22 ... => ...
  etc.

  For Bool, the constructors are false and true and don't have any args.
-/

theorem eqbAA : ∀ a : Bool, isTrue (eqb a a) := by
  intros a
  cases a with
  | false => -- suppose a is false
    simp

  | true => -- suppose a is true
    simp


theorem thmEqbAT : ∀ a : Bool, isTrue (eqb a true) → isTrue a := by
  intros a
  cases a with
    | false => -- suppose a is false
    unfold eqb
    unfold _root_.isTrue
    intro proofOfFalse
    cases proofOfFalse

    | true => -- suppose a is true
    unfold eqb
    unfold _root_.isTrue
    intro proofOfTrue
    exact True.intro


/-!
  Lean uses "inl" and "inr" instead of "or_introl" and "or_intror".

inductive Or (a b : Prop) : Prop where
| inl (h : a) : Or a b
| inr (h : b) : Or a b

Or's symbol is ∨, which is typed "\or".
-/

theorem leftOr : ∀ (A B : Prop), A → A ∨ B := by
  intros A B
  intros proofOfA
  let proofOfAOrB : A ∨ B := Or.inl proofOfA
  exact proofOfAOrB


theorem rightOr : ∀ (A B : Prop), B → A ∨ B := by
  intros A B
  intros proofOfB
  refine Or.inr ?_
  · exact proofOfB


theorem orCommutes : ∀ (A B : Prop), A ∨ B → B ∨ A := by
  intros A B
  intro AOrB
  cases AOrB with
    | inl proofOfA => -- I don't think I need the "suppose AOrB is ..."
    refine Or.inr ?_
    · exact proofOfA

    | inr proofOfB =>
    refine Or.inl ?_
    · exact proofOfB


/-!
inductive And (a b : Prop) : Prop where
| intro (left : a) (right : b) : And a b

And's symbol is ∧, which is typed "\and".
-/

theorem bothAnd : ∀ (A B : Prop), A → B → A ∧ B := by
  intros A B
  intros proofOfA proofOfB
  refine And.intro ?_ ?_
  · exact proofOfA

  · exact proofOfB


theorem andCommutes : ∀ (A B : Prop), A ∧ B → B ∧ A := by
  intros A B
  intro AAndB
  cases AAndB with
    | intro proofOfA proofOfB =>
    refine And.intro ?_ ?_
    · exact proofOfB

    · exact proofOfA

/- Lean doesn't have a destruct tactic.
   So there is no proof andCommutes__again.

   Perhaps my style should allow "cases .. with" on one line
   when there is only one constructor?
-/


/-
  Lean has operators for type Bool.

@[inline] def or (a b : Bool) : Bool :=
  match a with
  | true  => true
  | false => b

Or with Bool uses the symbol ||
infixl:65 " || " => OrOp.or


@[inline] def and (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false

And with Bool uses the symbol &&
infixl:70 " && " => AndOp.and


@[inline] def not : Bool → Bool
  | true  => false
  | false => true
prefix:100 "!" => Not.not


def Iff (a b : Prop) : Prop := (a → b) ∧ (b → a)

Iff's symbol is ↔, which is typed "\iff".
-/

/- Unfold Iff didn't work in this proof.
   I eventually used "refine Iff.intro ?_ ?_"
   Not a fan of it.

  Doing cases on two variables at the same time is done with:
     cases a <;> cases b
  But then you cannot use "with" with them.

  The <;> connector runs the second tactic on each subgoal of the first tactic.

  I don't find this simple proof very readable.
-/

theorem boolOrIsOr :
  ∀ a b : Bool, isTrue (a || b) ↔ isTrue a ∨ isTrue b := by
  intros a b
  -- unfold Iff
  refine Iff.intro ?_ ?_

  -- direction: isTrue (a || b) → isTrue a ∨ isTrue b
  · intro H
    cases a <;> cases b

    -- case a = false, b = false
    · unfold _root_.isTrue at H
      simp at H
      -- simp solve this ... it would look better if cases solved it.

    -- case a = false, b = true
    · unfold _root_.isTrue
      exact Or.inr True.intro

    -- case a = true, b = false
    · unfold _root_.isTrue
      exact Or.inl True.intro

    -- case a = true, b = true
    · unfold _root_.isTrue
      exact Or.inl True.intro

  -- direction: isTrue a ∨ isTrue b → isTrue (a || b)
  · intro H
    cases a <;> cases b

      -- case a = false, b = false
    · cases H with
      | inr B =>
      unfold _root_.isTrue at B
      cases B

      | inl A =>
      unfold _root_.isTrue at A
      cases A

    -- all other cases
    · unfold _root_.isTrue
      exact True.intro
    · unfold _root_.isTrue
      exact True.intro
    · unfold _root_.isTrue
      exact True.intro



theorem andbIsAnd : ∀ a b : Bool, isTrue (a && b) ↔ isTrue a ∧ isTrue b := by
  intros a b
    -- unfold Iff
  refine Iff.intro ?_ ?_

    -- direction: isTrue (a && b) → isTrue a ∧ isTrue b
  · intro H
    cases a <;> cases b

    -- a = false, b = false
    · unfold _root_.isTrue at H
      simp at H

    -- a = false, b = true
    · unfold _root_.isTrue at H
      simp at H

    -- a = true, b = false
    · unfold _root_.isTrue at H
      simp at H

    -- a = true, b = true
    · unfold _root_.isTrue
      exact And.intro True.intro True.intro

    -- direction: isTrue a ∧ isTrue b → isTrue (a && b)
  · intro H
    cases a <;> cases b

    -- a = false, b = false
    · unfold _root_.isTrue at H
      cases H with
      | intro A B => cases A

    -- a = false, b = true
    · unfold _root_.isTrue at H
      cases H with
      | intro A B => cases A

    -- a = true, b = false
    · unfold _root_.isTrue at H
      cases H with
      | intro A B => cases B

    -- a = true, b = true
    · unfold _root_.isTrue
      exact True.intro


/-
  Lean uses the funny "sorry" instead of Coq's "admit".
-/

theorem negbIsNot : ∀ a : Bool, isTrue (!a) ↔ ¬ isTrue a := by
  sorry


/-!
inductive Exists {α : Type} (P : α → Prop) : Prop where
| intro (w : α) (h : P w) : Exists P

Exists's symbol is ∃, which is typed "\exists".
-/

def basicPredicate : Bool → Prop :=
  fun a => isTrue (a && true)


theorem thmExistsBasics : ∃ x, basicPredicate x := by
  let witness := true
  apply Exists.intro witness
  unfold basicPredicate
  unfold _root_.isTrue
  exact True.intro


theorem thmExistsBasics__again : ∃ x, basicPredicate x := by
  let witness := true
  refine Exists.intro witness ?_
    -- Wanted to use simp, but it doesn't do what "simpl" does in Coq.
  · exact True.intro


theorem thmForallExists : ∀ b : Bool, ∃ a : Bool, isTrue (eqb a b) := by
  intro b
  cases b with
    | false =>
    let witness := false
    refine @Exists.intro Bool (fun a => _root_.isTrue (eqb a false)) witness ?_
    · unfold _root_.isTrue
      simp  -- wish this did more computation
      exact True.intro

    | true =>
    let witness := true
    refine @Exists.intro Bool (fun a => _root_.isTrue (eqb a true)) witness ?_
    · unfold _root_.isTrue
      simp  -- wish this did more computation
      exact True.intro


theorem thmForallExistsAgain : ∀ b : Bool, ∃ a : Bool, isTrue (eqb a b) := by
  intro b
  refine @Exists.intro Bool (fun a => isTrue (eqb a b)) b ?_  -- witness is b
  · exact eqbAA b


/- Cases is doing a lot of work.
   It ends proofs of False.
   It branches for types with multiple constructors
   and it handles a single constructor, like Exists.

   I think of those as very separate concepts.
   I like that Coq has a "destruct" tactic for the last.
   When you see "destruct" there is no reason to indent.
-/

theorem forallExists: ∀ (P : Type → Prop), (∀ x, ¬ P x) → ¬ (∃ x, P x) := by
  intros P
  intros forallXNotPx
  unfold Not
  intro existsXPx
  cases existsXPx with
    | intro witness proofOfPwitness =>
    let notPwitness := forallXNotPx witness
    unfold Not at notPwitness
    let proofOfFalse := notPwitness proofOfPwitness
    cases proofOfFalse


theorem existsForall : ∀ (P : Type → Prop), ¬ (∃ x, P x) → ∀ x, ¬ P x := by
  intros P
  intros notExistsXPx
  intros x
  unfold Not
  intro Px
  unfold Not at notExistsXPx
  apply notExistsXPx
  exact Exists.intro x Px


/-!
  inductive Eq {α : Sort u} (a : α) : α → Prop where
    | refl : Eq a a

x = y  ≡  Eq x y
-/

/- Again, when there is a single constructor, like refl,
   Coq's "destruct" just looks better.

  Here, I just didn't indent the single case.  But it feels off.

   Notice that in Lean, the constructor is "refl"
   but the tactic to solve it is "rfl".
-/

theorem eqSym : ∀ (x y : Type), x = y → y = x := by
  intros x y
  intros xEqualsY
  cases xEqualsY
  exact Eq.refl x


theorem eqTrans : ∀ (x y z : Type), x = y → y = z → x = z := by
  intros x y z
  intros xEqY yEqZ
  cases xEqY
  cases yEqZ
  exact Eq.refl x


/-!
  The "rewrite" tactic does a rewrite.
  The "rw" tactic does a rewrite AND tries to solve simple goals.

  So, most people will use "rw" but I use "rewrite" here for precision.
-/

theorem eqTransAgain : ∀ (x y z : Type), x = y → y = z → x = z := by
  intros x y z
  intros xEqY yEqZ
  rewrite [xEqY]
  rewrite [← yEqZ]
  exact Eq.refl y


theorem andbSym : ∀ a b : Bool, (a && b) = (b && a) := by
  intros a b
  cases a <;> cases b

  -- suppose a = false, b = false
  · simp
    -- exact Eq.refl false

  -- suppose a = false, b = true
  · simp

  -- supposea = true, b = false
  · simp

  -- suppose a = true, b = true
  · simp

/-!
  def Ne {α : Sort u} (a b : α) : Prop :=
    ¬ (a = b)
  notation:50 lhs:50 " ≠ " rhs:50 => Ne lhs rhs
-/

/-
  I don't like that I need to know the name of the
  type behind ↔ and ≠ unorder to unfold them.

  "contradiction" will check all hypotheses for
  any that cannot be constructed.  It is like using
  a shotgun instead of Coq's "discriminate".
-/

theorem neqNegA : ∀ a : Bool, a ≠ !a := by
  intro a
  unfold Ne
  unfold Not
  cases a with
    | false =>
    intro aEqNegA
    change false = true at aEqNegA --- I don't like this at all!
    contradiction -- this checks all hypotheses.

    | true =>
    intro aEqNegA
    change true = false at aEqNegA
    contradiction -- this checks all hypotheses.


/-!
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
-/

theorem plus2_3 : Nat.succ (Nat.succ 0) + Nat.succ (Nat.succ (Nat.succ 0)) = Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) := by
  simp
  -- simp solves the goal ... you cannot see the outcome and then run "exact".


theorem plusO_n : ∀ n : Nat, 0 + n = n := by
  intros n
  simp
  -- simp solves the goal... sigh.


/- Lean's tactic is called "induction".
-/

theorem plusN_O : ∀ n : Nat, n + 0 = n := by
  intros n
  induction n with
  | zero =>
    simp
    -- again, no need for exact.
  | succ n' ih =>
    simp
    -- WTF.  I don't like this at all.  There is no way to get the fine control I want.


/- I was having trouble proving that plus is commutative,
  so I reproved this theorem using a direct call to the
  induction function: Nat.rec.
-/
theorem plusN_O__again : ∀ n : Nat, n + 0 = n := by
  intros n
  refine Nat.rec ?_ ?_ n
  · rfl

  · intros n' ih
    simp


/-! Lean defines addition by induction on the second argument,
  which is different from Coq.
-/
#print Nat.add

/- So, induction on the second argument, m, before the first, n.

  This took a while for me to get right.  The trick was to
  make the induction less powerful, using "clear ih_m" after
  I used the inductive hypothesis.  (I don't know why I didn't
  have to do that in Coq.)
-/

theorem plusSym : ∀ n m : Nat, n + m = m + n := by
  intro n m
  induction m with
    | zero =>
    -- base case: n + 0 = 0 + n
    induction n with
      | zero =>
      -- base case: 0 + 0 = 0 + 0
      rfl

      | succ n' ih =>
      -- inductive step: (n'+1) + 0 = 0 + (n'+1)
      change n' + 1 = (0 + n') + 1
      rewrite [← ih]
      change n' + 1 = n' + 1
      rfl
    | succ m' ih_m =>
    -- inductive step: n + (m'+1) = (m'+1) + n
    change (n + m') + 1 = m' + 1 + n
    rw [ih_m]
    clear ih_m  --- THIS WAS THE KEY TO MAKING IT WORK!
    induction n with
      | zero =>
        rfl

      | succ n' ih_n =>
        change (m' + n') + 1 + 1 = ((m' + 1) + n') + 1
        rw [ih_n]


/- I was having trouble proving that plus is commutative,
  so I proved the theorem first using a direct call to the
  induction function: Nat.rec.   I then was able to fix
  my original proof above.
-/
theorem plusSym__again : ∀ n m : Nat, n + m = m + n := by
  intro n m
  refine Nat.rec ?_ ?_ m
  -- base case: n + 0 = 0 + n
  . refine Nat.rec ?_ ?_ n
    -- base case: 0 + 0 = 0 + 0
    . rfl

    -- inductive step: (n'+1) + 0 = 0 + (n'+1)
    . intros n' ih_n
    -- n'.succ + Nat.zero = Nat.zero + n'.succ
      change n'.succ = Nat.zero + n'.succ
      change n'.succ = (Nat.zero + n').succ
      rewrite [← ih_n]
      rfl

  -- inductive case for m
  . intros m ih_m
    change (n + m).succ = m.succ + n
    rewrite [ih_m]
    clear ih_m
    refine Nat.rec ?_ ?_ n

    -- base case: 0 + (m.succ) = (m.succ) + 0
    · rfl

    -- inductive step: (n'+1) + (m.succ) = (m.succ) + (n'+1)
    . intros n' ih_n
      change ((m + n').succ).succ = m.succ + n'.succ
      change ((m + n').succ).succ = (m.succ + n').succ
      rewrite [ih_n]
      rfl


theorem minusIsFunny : 0 - 1 = 0 - 2 := by
  simp
  -- exact Eq.refl 0

/-!
inductive List (α : Type u)
| nil  : List α
| cons : α → List α → List α

List.length
-/

theorem consAddsOneToLength :
  ∀ (A : Type) (x : A) (lst : List A), (x :: lst).length = lst.length + 1 := by
  intros A x lst
  simp


def hd (α : Type) (default : α) (l : List α) : α :=
  match l with
  | []     => default
  | x :: _ => x

def myHdForNatLists := hd Nat 0

#eval myHdForNatLists []             -- 0
#eval myHdForNatLists [5, 4]         -- 5

/- These "rfl" seem to do too much work.
-/

theorem correctnessOfHd :
  ∀ (A : Type) (default x : A) (lst : List A),
    hd A default [] = default ∧
    hd A default (x :: lst) = x := by
  intros A default x lst
  apply And.intro
  · rfl

  · rfl


/-!
Definition head (A : Type) (l : list A)
:=
  match l with
    | nil => None
    | x :: _ => Some x
  end.
-/

/- I'm not sure this is the best way to pass Nat to List.head.
-/
#eval List.head? (α := Nat) []             -- None
#eval List.head? [5, 4]                    -- Some 5

theorem correctnessOfHead? :
  ∀ (A : Type) (x : A) (lst : List A),
    List.head? ([] : List A) = none ∧
    List.head? (x :: lst) = some x := by
  intros A x lst
  apply And.intro
  · rfl

  · rfl

/-! This function was MUCH easier to write in Lean.
    (With ChatGPT's help.)

    It is finally the first thing in Lean that was an
    improvement in clarity over Coq.
-/
def hdNeverFail (α : Type) (lst : List α) (safetyProof : lst ≠ []) : α :=
  match lst with
  | []      => nomatch safetyProof rfl
  | x :: _  => x

theorem correctnessOfHdNeverFail :
  ∀ (A : Type) (x : A) (rest : List A),
    ∃ (safetyProof : (x :: rest) ≠ []),
      hdNeverFail A (x :: rest) safetyProof = x := by
  intros A x rest
  let witness : (x :: rest) ≠ [] := by
    intro h
    contradiction
  apply Exists.intro witness
  rfl


/- I didn't like using Lean.  For getting to understand the
  low-level how-it-actually-works, users need precise commands.
  Especially one that just runs all the functions in the goal
  without solving it.  "Simp" solves the goal, which hides
  what is going on.

  I believe you can write your own Lean tactics.  Perhaps I
  should try if I want to turn this into a full tutorial where
  users can understand low-level Lean.
  -/

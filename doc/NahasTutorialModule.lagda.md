# An Agda Experiment
by Michael Nahas

Started 2021-Oct-31

Version 1 2021-Nov-3

------------------------------

I wanted to learn Agda.  I decided to do that by
translating all the proofs from my Coq tutorial into
Agda.

This file contains all those proofs.  It is NOT meant
to be an Agda tutorial.  It is just a cheatsheet for
me if I ever want to use Agda in the future.  I'm making
the file available in case anyone who liked my Coq tutorial
wanted to see what Agda was like.  

Agda is different than Coq.  Coq uses tactics to generate the proofs.
The proofs are actually functions, but the code of those functions is
hidden from the user.  Agda writes the proof functions directly.
Instead of tactics, it uses commands in its Emacs mode to help users
write the proofs.  So, you really need to write Agda in a smart editor
like Emacs.


## Location of file and generating

The latest version of this file is available on my website.
[HTML](https://mdnahas.github.io/doc/NahasTutorialModule.html)
[Agda](https://mdnahas.github.io/doc/NahasTutorialModule.lagda.md)

To generate the HTML file, I used Agda's literate programming
feature with Markdown.  I generate it by running:

`agda -i /usr/share/agda-stdlib/ --html --html-highlight=code NahasTutorialModule.lagda.md`

`markdown html/NahasTutorialModule.md > NahasTutorialModule.html`


## Resources

[Agda Emacs Mode commands](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)

[List of operators in Agda](https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html)

In Agda's Emacs mode, you can middle-click on a goal and you will get
a context menu with the possible commands.  This is very useful when
you're not sure what to do next.

In Agda's Emacs mode, if you want to figure out how to type a
character, you can do "M-x describe-char" or "C-u C-x =".  That
command generates a lot of output, but one line will say something
like "to input: type "\union" or "\u+" or "\uplus" with Agda input
method"


```agda

{- Comments -}
{- Comments start with a '{' followed by a '-'.  
 and end with a '-' followed by a '}'.
-}

-- You can also do single-line comments, where the line starts with two '-'s.

```

## Modules

Agda files must start with a module declaration.  The name of the
module must match the name of the file.

```agda

module NahasTutorialModule where

```

## Basics

This is how to write an inductive type.  NOTE: the spaces around the ':' are important!

```agda

data Bool : Set where
  true : Bool
  false : Bool

```

This is a function.  Function implementation is done by case matching. The single equal sign '=' is definitional.

```agda

not : Bool → Bool
not true = false
not false = true

```

Adga allows unicode.  The right arrow above could be typed "->"
or it can be entered using the LaTeX-like sequence
"\to" which will be automagically converted to the
right arrow you see above.  

Enter "→" with "\to".

In Emacs, use "C-c C-l" to "load" the file.  This will have the Agda
compiler parse the file and show you all the errors, etc..

To test a definition of a function, you can use "C-c C-n".
You can then type in a value like "not true" and it will
be evaluated to "false".


```agda

¬¬ : Bool → Bool
¬¬ b = not (not b)

```

Enter '¬' with "\neg".

Note that "¬¬" is a single operator, even though it is 2 characters.

If you enter
<br>`¬¬ b = ?`<br>
and do "C-c C-l", you get:
<br>`¬¬ b = { }0`<br>

The `{ }0` is a "hole" and, in this case, hole number 0.
(You can have multiple holes.)

The idea is that the hole is something to fill in later.
The type checker can identify the type of the hole and
help you fill it in.
Another window will open up that tells you the type of
the hole: "`?0 : Bool`", meaning hole number 0 has type
"Bool".

So if you enter:
<br>`¬¬ b = {not ? }0`<br>
It means that you want to replace the hole by "not ?" 
And when do "C-c C-l", then you get:
<br>`¬¬ b = not { }1`<br>
That is, it has accepted the "not" and created a new
hole, which is now hole number 1.

Next:
<br>`¬¬ b = not {not ?}1`<br>
becomes 
<br>`¬¬ b = not (not { }2)`<br>
and then
<br>`¬¬ b = not (not {b }2)`<br>
does nothing with "C-c C-l".

This is because "b" has the appropriate type.  To get rid of
the hole, you need to use "C-c spacebar".
Then you get:
<br>`¬¬ b = not (not b)`<br>

Coq: "C-c spacebar" is like "exact".


## Proofs

I'm trying to learn how to prove in Agda, so let's try a proof.
A proof is a function

```agda

myFirstProof : (A : Set) → A → A
myFirstProof A proofofA = proofofA

```

A proof is a function, so it looks like "not" that was written above.
Here, the proof takes a proposition "A" and a proof of that
proposition, and returns the proof of the proposition.

If you enter
<br>`myfirstproof A proofofA = ?`<br>
And do "C-c C-l"
you'll get a hole.
<br>`myfirstproof A proofofA = {!!}0`<br>
and, with the cursor in the hole, "C-c C-e" will show the context
("e" is meant to mean "environment").
Since the hole is type "A" and you have "proofofA" in the environment,
typing "proofofA" and "C-c C-spacebar" will solve the proof.


If instead you started with
<br>`myfirstproofagain = ?`<br>
You can do "C-c C-c enter" and Agda will automatically change it to
<br>`myfirstproofagain A x = ?`<br>
And then you can follow the proof as above.

Coq: If you want "intros", do "C-c C-c enter"

```agda

backwardsSmall : (A B : Set) → A → (A → B) → B
backwardsSmall A B a atob = atob a

```

To solve this, I did "C-c C-e" to look at the context ("environment")
Saw I had a function "`atob : A → B`"
Typed "atob" in the hole and hit "C-c C-r".  This is the "refine"
command and it applies a function and creates hole for every argument
to the function.

Coq: "refine" or "apply" is enter the name of the function in the hole
and enter "C-c C-r".

Proving backwards tries to keep making the goal simpler.  We can also
prove going forwards, where we keep adding terms to the context
("environment") until we build up a term with the same type as the goal.

```agda

forwardSmall : (A B : Set) → A → (A → B) → B
forwardSmall A B a atob = let b = atob a in b

```

To prove in the forward direction, I filled the hole with
"`let b = atob a in ?`".
After hitting "C-c C-spacebar", the context now had a term "b : B"
and since that matched the goal, I could enter "b" and then
type "C-c C-spacebar" to finish the proof.

```agda

backwardsLarge : (A B C : Set) → A → (A → B) → (B → C) → C
backwardsLarge A B C a atob btoc = btoc (atob a)

forewardsLarge : (A B C : Set) → A → (A → B) → (B → C) → C
forewardsLarge A B C a atob btoc = let b = atob a in let c = btoc b in c


backwardsHuge : (A B C : Set) → A → (A → B) → (A → B → C) → C
backwardsHuge A B C a atob aandbtoc = aandbtoc a (atob a)

```

The only difference here is that when you enter "aandbtoc"
into the initial hole and hit "C-c C-r", there are 2 holes
created. 
<br>`backwardshuge A B C a atob aandbtoc = aandbtoc { }2 { }3`<br>
The other window shows the type of each.  By looking at the
context, we can find variables or functions to supply
the type of each.


## Unit and Empty types 

The Unit type has only one constructor.  

The Empty type has none.

Using the BHK interpretation, we can use the Unit type in place
of "true" and "Empty" in place of "false" in many logic statements.
We need to replace "implication" with the function type →.

```agda

record ⊤ : Set where
  constructor tt

```

Enter '⊤' with "\top".

A "record" is the same as "data", but with only 1 constructor.
The constructor is "tt".

Later on, instead of using "tt", you can also use "record {}".  That
can be used for any record, with the record's parameters inside the
curly braces.  Agda can figure out the correct constructor from the
type of the hole.

Agda does have "Prop", which is similar to "Set" but is
"proof irrelevant".  But using it requires using a command-line
argument with Agda and I wasn't sure how to do that in Agda's
Emacs mode.

Agda's Sets have a index associated with them.  It allows a Set in a
higher universe to contain Sets in the lower universe.  I found the
indices added a lot of confusion to types and didn't add much, so for
this file I've deleted them.  

```agda


data ⊥ : Set where

```

Enter '⊥' with "\bot".

This type has no constructors.

```agda

trueCanBeProven : ⊤
trueCanBeProven = tt

```

I'm actually not sure if there's a Agda Emacs-mode command
that solves this.  I tried "C-c C-c", since there is only 1
constructor (one case), but that didn't work.  It actually
DELETED the line "`trueCanBeProven = ?`"!

I was able to use the automatic solver, "C-c C-a".

Definition of "not" for types 

```agda

¬_ : Set → Set
¬ A = A → ⊥

```

Enter '¬' with "\neg".

```agda

falseCannotBeProved : ¬ ⊥
falseCannotBeProved proofoffalse = proofoffalse

```

This is pretty much a normal proof now.
"C-c C-c enter" will add the argument that I renamed "`proofoffalse`".
then that is an exact match for the goal.

In Agda, it is harder to see that "¬" is actually a function
and takes an argument.  But the proof is easy after that.

```agda

falseCannotBeProvedAgain : ¬ ⊥
falseCannotBeProvedAgain ()

```

This is the other proof, where I do cases on the argument "proofoffalse".
That is accomplished by entering "proofoffalse" in the hole and then
entering "C-c C-c".
It results in "falseCannotBeProvedAgain ()" which is Agda's notation
for a definition where there are no cases because the particular argument
has no possible instances.

```agda

trueImpliesTrue : ⊤ → ⊤
trueImpliesTrue a = a

falseImpliesTrue : ⊥ → ⊤
falseImpliesTrue proofoffalse = tt

falseImpliesFalse : ⊥ → ⊥
falseImpliesFalse () 

```

Wow!  I was able to write those directly, without any help!

```agda

trueImpliesFalse : ¬(⊤ → ⊥)
trueImpliesFalse truetofalse = truetofalse tt

```

It took a little longer to prove this one, but not too bad.

```agda

absurdHelper : (C : Set) → ⊥ → C
absurdHelper C ()

absurd : (A C : Set) → A → (¬ A) → C
absurd A C proofofA proofthatAcannotbeproven = let proofoffalse = proofthatAcannotbeproven proofofA in absurdHelper C proofoffalse

absurdAgain : (A C : Set) → A → (¬ A) → C
absurdAgain A C proofofA proofthatAcannotbeproven = absurdHelper C (proofthatAcannotbeproven proofofA)

```

I found out that you can do local definitions with "where", so the following version hides the definition of the helper function.

```agda

absurdAgainAgain : (A C : Set) → A → (¬ A) → C
absurdAgainAgain A C proofofA proofthatAcannotbeproven = let proofoffalse = proofthatAcannotbeproven proofofA in absurdHelper2 C proofoffalse
  where
  absurdHelper2 : (C : Set) → ⊥ → C
  absurdHelper2 C ()

```

And you can use "with" to create a dummy parameter to the function, where they dummy's value is a function of the other parameters.


```agda

absurdAgainAgainAgainAgain : (A C : Set) → A → (¬ A) → C
absurdAgainAgainAgainAgain A C proofofA proofthatAcannotbeproven with proofthatAcannotbeproven proofofA
absurdAgainAgainAgainAgain A C proofofA proofthatAcannotbeproven | ()


```

A function mapping true to an inhabited type and false to an empty
type.

```agda

T : Bool → Set
T true  = ⊤
T false = ⊥


trueIsTrue : T true
trueIsTrue = tt

```

If you do "C-c C-t" in the hole, it show you the simplified type
of the goal.  In the above proof, it was just "⊤".  So I filled in "tt".

```agda

eqb : Bool → Bool → Bool
eqb true  true  = true
eqb true  false = false
eqb false true  = false
eqb false false = true

notEqbTrueFalse : ¬(T (eqb true false))
notEqbTrueFalse ()

```

I took some time to figure out what was happening here.  But the value
resolved to type ⊥ and I could say there could be no argument of that
type.

```agda

eqbaa : (a : Bool) → (T (eqb a a))
eqbaa true = tt
eqbaa false = tt

```

Simple proof by cases.

```agda

eqbat : (a : Bool) → (T (eqb a true)) → (T a)
eqbat true x = tt

```

When I split on cases of "a", there was only 1.
The simplified goal shown by "C-c C-t" showed it was type "⊤",
which is solved by "tt".

"or" in Agda is the Sum type.

```agda

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

```

Enter '⊎' with "\u+" or "\uplus".
Enter "inj₁" with "inj\_1".

```agda

leftOr : (A B : Set) → A → (A ⊎ B)
leftOr A B a = inj₁ a

orCommutes : (A B : Set) → (A ⊎ B) → (B ⊎ A)
orCommutes A B (inj₁ a) = inj₂ a
orCommutes A B (inj₂ b) = inj₁ b

data _×_ (A B : Set) : Set where
  _,′_ : A → B → A × B

```

Enter '×' with "\x".
Enter '′' with "\prime" or "\'1"

```agda

bothAnd : (A B : Set) → A → B → A × B
bothAnd A B a b = a ,′ b

```

Eventually was able to put "_,′_" in the hole and use "C-c C-r"

```agda

andCommutes : (A B : Set) → (A × B) → (B × A)
andCommutes A B (a ,′ b) = b ,′ a

_&&_ : Bool -> Bool -> Bool
_&&_ true true = true
_&&_ _ _ = false

```

If you put _ in a definition, it matches all other cases.

```agda

_||_ : Bool -> Bool -> Bool
_||_ false false = false
_||_ _ _ = true

```

I found the following definition of iff on a webpage, not the standard library

```agda

_iff_ : Set → Set → Set
_iff_ A B = (A → B) × (B → A)

orbIsOrHelper : (A B : Set) -> (A ⊎ B) → ⊤
orbIsOrHelper _ _ _ = tt

orbIsOrHelper2 : (⊥ ⊎ ⊥) → ⊥
orbIsOrHelper2 (inj₁ x) = x
orbIsOrHelper2 (inj₂ y) = y

orbIsOr : (a b : Bool) → T (a || b) iff (T a ⊎ T b)
orbIsOr true true = inj₁ ,′ orbIsOrHelper ⊤ ⊤
orbIsOr true false = inj₁ ,′ orbIsOrHelper ⊤ ⊥
orbIsOr false true = inj₂ ,′ orbIsOrHelper ⊥ ⊤
orbIsOr false false = inj₁ ,′ orbIsOrHelper2

```

At this point in the Coq tutorial, I wrote a comment saying "we're not
in Kansas any more!"  And I definitely feel that here too.  I needed two
helper functions.  It doesn't feel as understandable as the Coq proof.
I cannot follow it.

I didn't seem as easy to split the proof into two directions (left
implies right and right implies left).  Can I do it that way?  Let me
try...

```agda

andbIsAndLeft : (a b : Bool) → T (a && b) → (T a × T b)
andbIsAndLeft true true x = tt ,′ tt

andbIsAndRight : (a b : Bool) → (T a × T b) → T (a && b)
andbIsAndRight true true (tt ,′ tt) = tt

andbIsAnd : (a b : Bool) → T (a && b) iff (T a × T b)
andbIsAnd a b = (andbIsAndLeft a b) ,′ (andbIsAndRight a b)


```

It wasn't hard to do it that way.  Agda took care of a lot
of the cases because they weren't possible.  There are no
instances of ⊥.

## Existence

```agda

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

```

Enter 'Σ' with "\Sigma".

```agda

∃ : ∀ {A : Set} → (A → Set) → Set
∃ = Σ _

```

Enter '∃' with "\ex".

Notice the curly braces in "{A : Set}".  That makes the argument
implicit.  The compiler can determine it from the type of the next
argument "A → Set".

```agda

basicPredicate : Bool -> Set
basicPredicate a = T (a && true)

existsBasics : ∃ basicPredicate
existsBasics = true , tt

```

I solved this by putting the cursor in the old and typing "_,_"
followed by "C-c C-r".  Agda's Emacs mode created the pair.

"C-c C-t" did not fully evaluate the goal.  It's type was
"`basicPredicate true`".
I was able to use "C-c C-n" to evaluate "`basicPredicate true`"
as ⊤ and then supply "tt" as the second have of the pair.

```agda

existsBasicsAgain : ∃ (\ a → T (a && true))
existsBasicsAgain = true , tt

```

Lambda terms (a.k.a. nameless functions) are written "\ variablename → expression".

```agda

forallExists : (b : Bool) → ∃ (\ a → T (eqb a b))
forallExists true = true , tt
forallExists false = false , tt

```

Strange that each case has enough information to evaluate down to ⊤
But, then again, the Coq proof is a case followed by simplification
and "exact I".

```agda

forallExists2 : (b : Bool) → ∃ (\ a → T (eqb a b))
forallExists2 b = b , eqbaa b

```

Reusing earlier proof.  Was able to type it in directly.

```agda

forallExistsSet : (A : Set) → (P : A → Set) → (∀ x → ¬ P x) → ¬ (∃ (\ x → P x))
forallExistsSet A P forallxnotPx (x , Px) = let notPx = forallxnotPx x in absurd (P x) ⊥ Px notPx

```

It took me a while to translate this statement from Coq to Agda.
I had to introduce "A : Set" to make it work.  I don't think I
lost much.

I'm still a little confused by ∀ in Agda.  It took me a while to
realize that I needed it before x.

Needed to use "absurd" because I cannot do case-of-false in Agda.

Really should use "{}" to make sets implicit in "absurd".  It took
some time to figure those out.  Mostly, I figured it out because
of good error messages.

```agda

existsForallSet : (A : Set) → (P : A → Set) → ¬ (∃ (\ x → P x)) → (∀ x → ¬ P x)
existsForallSet A P notexistxPx x Px = notexistxPx (x , Px)

```

This was actually pretty easy.

Agda has an alternative syntax for Sigma types, declared with the syntax keyword.

```agda

syntax Σ A (λ x → B) = [ x ∈ A ] B

```

## Equality

We can import Agda's equality operator with this import:

```agda

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

```

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

Enter "≡" with "\==".

```agda

equalityIsSymmetric : {A : Set} → {x : A} → {y : A} → x ≡ y → y ≡ x
equalityIsSymmetric refl = refl

```

Because "x ≡ y" has only one possible case for its constructor, that
must "unify" x and y to be the same.  The goal becomes something of
type "x ≡ x", which is solved by refl.

I didn't find an equivalent to "destruct" in Agda's Emacs mode.

```agda

equalityIsTransitive : {A : Set} → {x : A} → {y : A} → {z : A} → x ≡ y → y ≡ z → x ≡ z
equalityIsTransitive refl refl = refl

```

Agda's Emacs mode inserted the ".x" when I entered x≡y followed by
"C-c C-c".  The "." means that the parameter is "inaccessible".  I'm
not sure exactly what that means.  The manual says that Agda confirms
the type, but doesn't check all the cases.  I guess that "refl"
determines the value for the ".x" parameters and Agda can figure out
that all cases are handled.

In Coq, I also proved this theorem by rewriting.  I'm not sure how to
do that in Agda, yet.  (NOTE: I later figured out that Agda doesn't
have rewriting.  More on that later.)


```agda

andbSymmetric : (a : Bool) → (b : Bool) → ( a && b ) ≡ ( b && a )
andbSymmetric true true = refl
andbSymmetric true false = refl
andbSymmetric false true = refl
andbSymmetric false false = refl

```

Pretty easy, just handle each case.


```agda

_≢_ : {A : Set} → A → A → Set
_≢_ x y = ¬ (x ≡ y)


```

Enter '≢' with "\==n"

It took me a while to figure out what that definition had to be.

```agda

negNega : (a : Bool) → (a ≢ (not a))
negNega true ()
negNega false ()

```

Strange.  I needed two lines here.  With two lines, the compiler is
able to determine that each is absurd, but when I had a single line,
it was not able to do it.  But, I guess Coq was similar, in that I
needed to do "case a" first too.


## Natural Numbers and Induction

```agda

import Data.Nat
open Data.Nat using (ℕ; zero; suc; _+_)

```

The "import" command loads Modules from a different file into this one.

The "open" command pulls names from another scope into this one.

They can be combined into a single line "open import Data.Nat using ..."

The module Data.Nat has the following definitions:

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

Enter 'ℕ' with "\bN".

```agda

plusTwoThree : ((suc (suc zero)) + (suc (suc (suc zero)))) ≡ (suc (suc (suc (suc (suc zero)))))
plusTwoThree = refl

```

The module also declares these types "built-in" with the line:
<br>`{-# BUILTIN NATURAL ℕ #-}`<br>

That is important, because it means that numbers like "2" can be
interpreted as an ℕ and that Agda's compilers will perform operations
on ℕ in proofs.

```agda

plusTwoThreeAgain : ( 2 + 3 ) ≡ 5
plusTwoThreeAgain = refl

```

Using "C-c C-t" I could see that the type of the goal was
<br>`(suc (suc (suc (suc (suc zero))))) ≡ (suc (suc (suc (suc (suc zero)))))`<br>
So, I entered "refl" and "C-c C-spacebar".  Agda must do simplification by execution.  

```agda

plusZeroN : (n : ℕ) → ( 0 + n ) ≡ n
plusZeroN n = refl

```

That's the simple one.  The next requires induction.

Induction in Agda is usually done using the congruence function, named
"cong".   We imported it when we imported the definition of _≡_ above.

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

```agda

plusNZero : (n : ℕ) → ( n + 0 ) ≡ n
plusNZero zero = refl
plusNZero (suc n′) = cong suc (plusNZero n′)

```

Obviously, the n=0 case is trivial, because it simplifies to 0=0.

The `n=(suc n′)` case is trying to prove `suc (n′ + 0) ≡ suc n′`.
Well, that's `(plusNZero n′)` with a "suc" on both sides of the equality.
So, we can construct that using the "cong" function with arguments
"suc" and `(plusNZero n′)`.  

The inductive case is usually (but I don't think always) written using
"cong".  The function definition does contain a recursive call to "plusNZero"
but its argument is not "n" but "n′".  Since "n′" is strictly smaller
than "n", the compiler can be sure that the recursive call is not part
of an infinite loop.

I'm not sure how it will work when the argument to the recursive call
is harder to determine to be smaller.

This is very different from Coq, where the induction hypothesis is
explicitly created when we do the "elim" command.  


Now, for the difficult proof: symmetry of addition.


First we import some operators used to prove a series of transitive
equalities.  Basically, they let you prove "a ≡ b" by a series of
small steps from "a" to "b". If Agda cannot figure out the step on its
own, you can provide the operations that make it possible.

This is not similar to Coq's "rewrite", because rewrite lets you work *inside* a term. 

```agda

-- uses this import from above: import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

exampleOfEqReasoning : ( 2 + 3 ) ≡ 5
exampleOfEqReasoning = begin
  2 + 3  {- left hand of what we're trying to prove -}
  ≡⟨⟩   
  ((suc (suc zero)) + (suc (suc (suc zero))))  {- first step -}
  ≡⟨ refl ⟩ {- reason for second step is "refl", but really isn't needed -}
    (suc ((suc zero) + (suc (suc (suc zero))))) {- second step -}
  ≡⟨⟩
    (suc (suc (zero + (suc (suc (suc zero)))))) {- third step -}
  ≡⟨⟩
    (suc (suc (suc (suc (suc zero))))) {- fourth step -}
  ≡⟨⟩
    5 {- right side of what we're trying to prove -}
  ∎
```

Enter '⟨' with "\<".
Enter '⟩' with "\>".
Enter '∎' with "\qed".

Next we prove a simple helper function.

```agda

plusSymmetricHelper : (n m : ℕ) → ( n + suc m ) ≡ suc ( n + m )
plusSymmetricHelper zero m = refl
plusSymmetricHelper (suc n′) m = cong suc (plusSymmetricHelper n′ m)

```

Lastly, the big theorem itself:

```agda

plusSymmetric : (n m : ℕ) → ( n + m ) ≡ (m + n)
plusSymmetric zero zero = refl
plusSymmetric zero (suc m′) = cong suc (equalityIsSymmetric (plusNZero m′))
plusSymmetric (suc n′) zero = cong suc (plusNZero n′)
plusSymmetric (suc n′) (suc m′) = cong suc (begin
  n′ + suc m′ 
  ≡⟨ plusSymmetricHelper n′ m′ ⟩
  suc (n′ + m′)
  ≡⟨ cong suc (plusSymmetric n′ m′) ⟩
  suc (m′ + n′)
  ≡⟨ equalityIsSymmetric (plusSymmetricHelper m′ n′) ⟩
    m′ + suc n′
  ∎)

```

The induction is done in the recursive call <br>`≡⟨ cong suc
(plusSymmetric n′ m′) ⟩`<br> Agda's equality reasoning is different
from Coq's.  Coq's "rewrite" command lets us change a value inside an
equation.  Agda only lets us show a chain of equal statements without
substitution inside the equations.  In Agda, if we want to do
substitution inside an equation, we need to use "cong".  Basically,
cong's second argument is the equality we want to substitute and
cong's first argument is a function that wraps that equality with the
rest of the statement we want to substitute it into.

## Data Types

We're going to be playing with Lists, so let's import Agda's list type.

```agda

--open import Data.List using (List ; []; _∷_)

--!!! I could not get official version to work.  I had to rename
-- "_::_" as "cons" to get it to work.
data List (A : Set) : Set where
  []  : List A
  cons : (x : A) (xs : List A) → List A

```

The official version has the definition:

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

So an instance of (List ℕ) might be "3 :: 2 :: 1 :: []".

```agda

length : {A : Set} → List A → ℕ
length [] = zero
length (cons a as) = suc (length as)

```

And the proof that adding an element increases a list's length by 1.

```agda

-- TODO: I only got Agda to accept the following by renaming "_::_" as "cons"
consAddsOneToLength : {A : Set} → (a : A) → (as : (List A)) → ((length (cons a as)) ≡ (suc (length as)))
consAddsOneToLength a as = refl

```

Now the three versions of head.

```agda

head1 : {A : Set} → (default : A) → (as : List A) → A
head1 default [] = default
head1 default (cons a as) = a

head1Correct : {A : Set} → (default : A) → (a : A) → (as : List A) → (((head1 default []) ≡ default) × ((head1 default (cons a as)) ≡ a))
head1Correct default a as = refl ,′ refl



data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

head2 : {A : Set} → (as : List A) → Maybe A
head2 [] = nothing
head2 (cons x as) = just x

head2Correct : {A : Set} → (a : A) → (as : List A) → (((head2 {A} []) ≡ nothing ) × ((head2 (cons a as)) ≡ just a))
head2Correct a as = refl ,′ refl

```

NOTE: Needed to pass Set A to head2 on an empty list to determine the type of the list.  That was done using "{}" to pass the implicit argument in an explicit fashion.

```agda

head3 : {A : Set} → (as : List A) → (as : (as ≢ [])) → A
head3 {A} [] as≢empty = absurdHelper A (as≢empty refl)
head3 {A} (cons a as′) as≢empty = a

consNeverEmpty : {A : Set} → (a : A) → (as : List A) → ((cons a as) ≢ [])
consNeverEmpty a as ()

--head3Correct : {A : Set} → (a : A) → (as : List A) → ∃ (\ (safetyproof : ((cons a as) ≢ [])) → ((head3 (cons a as) safetyproof) ≡ a))
--head3Correct : {A : Set} → (a : A) → (as : List A) → ( Σ ((cons a as) ≢ []) (\ safetyproof → ((head3 (cons a as) safetyproof) ≡ a)) )
head3Correct : {A : Set} → (a : A) → (as : List A) → [ safetyproof ∈ ( (cons a as ) ≢ ( [] {A} ) ) ]  ((head3 (cons a as) safetyproof) ≡ a)
head3Correct a as = consNeverEmpty a as , refl
                       
```

I had trouble understanding the error messages from Agda.  I forgot to add the argument "safetyproof" to the call to head3 and spent about 20 minutes trying to figure out what the problem was.   That's why there are 3 different version of exist here!

A final proof that cons-ing the head and tail of a list gets you back to the original list.

```agda

tail1 : {A : Set} → (as : List A) → List A
tail1 [] = []
tail1 (cons x as) = as

headTail : {A : Set} → (default : A) → (a : A) → (as : List A) → (cons (head1 default (cons a as)) (tail1 (cons a as))) ≡ (cons a as)
headTail default a as = refl

```

## Conclusions

There are a lot of differences between the languages.  

I loved Agda's Emacs mode.  The tactics are just key-combos, like "C-c C-c" for case, and you see the result right away.  It's much better than having to type out "case ..." in Coq.  I feel like tactics are operations and they better suited to being built into the user interface. 

I prefer Coq's ML-like language to Agda's Haskell-like language.  I'm much more familiar with OCaML and others like it.  But I went and read the Agda PhD thesis and I understand why they chose it.  It works well when working both forwards and backwards to assign types to expressions.  It did force me to write a lot of small helper functions, because I couldn't do "case proof_of_False" directly, like in Coq.  I know I could have defined a "case" operator, but it wouldn't have matched Agda's style.  I feel like Coq's proofs read much more like the proof style I'm used to in books.  

I felt that it was much harder to reason in Agda.  A lot of equality proofs were solved by just "refl", which was nice, but I never knew when that would happen.  In Coq's proofs, I used a specific subset of tactics because I knew I could control the result of them and know the state of the proof at each point.

A huge surprise for me was that, while the types of data and functions were essentially identical, there really wasn't a clear mapping of Coq proof to Agda proof and vice versa.  It would be hard to automatically translate from one to the other.  The proof that addition is symmetric was much easier to do in Agda than in Coq.  It did require helper functions and more operations, but I was never at risk of being lost in the proof.  I've seen an expert in Coq unable to prove symmetry of addition for 10 minutes!  Some proofs in Agda were more complicated and, often, required being split into multiple functions.  I only did simple induction proofs in Agda ... I am kinda of worried that more complicated ones would be difficult to do.  But, then again, simple ones in Coq were difficult, so maybe its less of a difference than I think.

It was much harder to write a "forward proof" in Agda.  The let expression exists, but it wasn't particularly easy to use.  

Coq's rewrite tactic is probably easier to use than Agda's sequence-of-transitive-equalities.  Agda can do the same things.  You just need to use "cong" every time you want to change a value inside an expression.  And that's got to be awkward to read and very awkward to write.  Coq's rewrite seems much simpler.

On a much lighter issue, I'm not sure where I stand with being able to type Unicode operators in Agda, vs. being stuck with plain text in Coq.  The biggest problem was that I could read some examples of Agda on the web, but not know how to type them in.  Eventually, I got used to it.  It saved screen real estate and it looked very mathy.  But I did have to memorize a lot of strange things like \'1 for "prime".  I will say that it was strange that Agda accepted both "->" and "→" as the same operator.  I would have just chosen one.  My problems with it could be fixed in the user interface, which might make it easier to search for and enter a symbol that you don't know.    (Although I wouldn't know where to search for '⊎'!)

The ",′" operator is just weird.  And I've never seen "⊎" before.  They seem like odd choice by the Agda library developers.

I did run into more issues with Agda.  They're listed below.  I filed bug reports for the ones I could reproduce.



## Agda bugs 


The statement:
<br>`syntax Σ A (λ x → B) = [ x ∈ A ] × B`<br>
on this page of the documentation:
<br> https://agda.readthedocs.io/en/v2.6.2/language/syntax-declarations.html <br>
is not accepted by Agda.


If you enter:
<br>`trueCanBeProven : ⊤`
<br>`trueCanBeProven = ?`<br>
And type "C-c C-c Enter", I expected it to be solved,
since there is only 1 constructor for ⊤.  But that didn't work.
It actually DELETED the line "`trueCanBeProven = ?`"!


I could not get Agda to accept this function type:
<br>`open import Data.List using (List ; []; _∷_)`
<br>`consAddsOneToLength : {A : Set} → (a : A) → (as : (List A)) → ((length (a :: as)) ≡ (suc (length as)))`<br>
It said "Not in scope:  ::"
It did not work when I used (_::_ a as).
It DID work when I defined a new list with "cons" instead of "_::_".

When I ran this file in Emacs mode, it was able to find the libraries just fine.
When I compiled the file on the command-line, I got
`Failed to find source of module`
`Relation.Binary.PropositionalEquality in any of the following`

UNABLE TO REPRODUCE:  Agda Emacs Mode does not handle empty agda code blocks in a literal Agda Markdown file.

UNABLE TO REPRODUCE
If you enter:
<br>`equality-is-symmetric : (A : Set) → (x : A) → (y : A) → x ≡ y → y ≡ x`
<br>`equality-is-symmetric A x y x-equals-y = ?`<br>
And then type "x-equals-y" followed by "C-c C-c", I expect it to
change the pattern to match the one possible constructor of equality,
which is "refl".  But it says:
Unbound variable x-equals-y
when checking that the expression ? has type x ≡ x
BUT
It did work with this one:
<br>`equalityIsTransitive : (A : Set) → (x : A) → (y : A) → (z : A) → x ≡ y → y ≡ z → x ≡ z`
<br>`equalityIsTransitive A x y z x≡y y≡z = ?`<br>

Feature Request: There are many "Nat": Builtin, Base, and Data.  The manual talks about how to write an import command, but not the standard library structure and how to use it.  

Feature Request: Emacs mode needs a command that takes a function type declaration
and creates the first line of definition.


import GlimpseOfLean.Library.Basic
import GlimpseOfLean.Library.Short

namespace Tutorial

/-
# Introduction

Lean is an interactive theorem prover, that is, a software that can be used to checked
the correctness of mathematical arguments.

The goal of this tutorial is to teach you how to read Lean code and to write down your
first proofs in Lean.

-/

/- # Examples from Calculus.

Let us see what a Lean proof looks like, without trying to understand any syntactical
detail yet.

We will use a lemma from calculus as an example; we first need to review some definitions.

-/

/-- A sequence `u` of real numbers converges to `l` if `∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| ≤ ε`.
This condition will be spelled `seq_limit u l`. -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) := -- in Lean, we write `l : ℝ` instead of `l ∈ ℝ`.
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-- A function`f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f(x) - f(x₀)| ≤ ε`.
This condition will be spelled `continuous_at f x₀`.-/
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

/-- Now we claim that if `f` is continuous at `x₀` then it is sequentially continuous
at `x₀`: for any sequence `u` converging to `x₀`, the sequence `f ∘ u` converges
to `f x₀`.
-/
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
  seq_limit (f ∘ u) (f x₀) := by { -- This `by` keyword marks the beginning of the proof
  -- Our goal is to prove that, for any positive `ε`, there exists a natural
  -- number `N` such that, for any natural number `n` at least `N`,
  --  `|f(u_n) - f(x₀)|` is at most `ε`.
  unfold seq_limit
  -- Fix a positive number `ε`.
  intros ε hε
  -- By assumption on `f` applied to this positive `ε`, we get a positive `δ`
  -- such that, for all real number `x`, if `|x - x₀| ≤ δ` then `|f(x) - f(x₀)| ≤ ε` (1).
  obtain ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε := hf ε hε
  -- The assumption on `u` applied to this `δ` gives a natural number `N` such that
  -- for every natural number `n`, if `n ≥ N` then `|u_n - x₀| ≤ δ`   (2).
  obtain ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ := hu δ δ_pos
  -- Let's prove `N` is suitable.
  use N
  -- Fix `n` which is at least `N`. Let's prove `|f(u_n) - f(x₀)| ≤ ε`.
  intros n hn
  -- Thanks to (1) applied to `u_n`, it suffices to prove that `|u_n - x₀| ≤ δ`.
  apply Hf
  -- This follows from property (2) and our assumption on `n`.
  apply Hu n hn
  -- This finishes the proof!
  }


/- # Now let's take a step back

I will now teach you about the ingredients needed to write such a proof in Lean.

Every command that is typed to make progress in a proof is called a “tactic”.
We will learn about a dozen of them. We want to replace each word `sorry` in this file by a
sequence of tactics that bring Lean to report there are no remaining goal, without
reporting any error along the way.

The opening and closing curly braces for each proof are not mandatory, but they help
making sure errors don’t escape your attention. In particular you should be careful
to check they are not underlined in red since this would mean there is an error.
-/

/- ## Computing

We start with basic computations using real numbers.

The tactic `ring` takes care of any proof that only uses basic properties of the addition and
multiplication in the real numbers (or in a commutative (semi)ring), such as commutatitivity
and associativity.

This tactic won’t use any assumption specific to the proof at hand.

-/

example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by {
  ring
}

/-
Our next tactic is the `congr` tactic (`congr` stands for “congruence”).
It tries to prove equalities by comparing both sides and creating new goals each time it
sees some mismatch.
-/

example (a b : ℝ) (f : ℝ → ℝ) : f ((a+b)^2) = f (a^2 + 2*a*b + b^2) := by {
  congr
  ring
}


/-
When there are several mismatches, `congr` creates several goals.
Sometimes `congr` is too eager; we can control this by limiting the number of function
application layers by putting a number after `congr`.
In the example the two functions that are applied are `f` and addition, and we want to
go only through the application of `f`.
-/

example (a b : ℝ) (f : ℝ → ℝ) : f (a + b) = f (b + a) := by {
  congr 1
  ring
}

/-
Actually `congr` does more than finding mismatches, it also try to resolve them
using assumptions. In the next example, `congr` creates the goal `a + b = c` by
matching, and then immediately proves it by noticing and using assumption `h`.
-/

example (a b c : ℝ) (h : a + b = c) (f : ℝ → ℝ) : f (a + b) = f c := by {
  congr
}

/-
The tactics `ring` and `congr` are the basic tools we will use to compute.
But sometimes we need to chain several computation steps (equalities or inequalities).
This is the job of the `calc` tactic.
-/

example (a b c : ℝ) (h : a = -b) (h' : b + c = 0) : b*(a - c) = 0 := by {
  calc
    b * (a - c) = b * (-b - c) := by congr
    _ = b * - (b + c) := by ring
    _ = b * - 0 := by congr
    _ = 0 := by ring
}

/-
The indentation rules for `calc` are a bit subtle, especially when there
are other tactics after `calc`. Be careful to always align the `_`.

You can use the `calc?` tactic to get started, and then putting the cursor after `:= by`
allows to select subterms to replace in a new calculation step.

Note that subterm selection is done using Shift-click.
-/
example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by {
  calc
    c = b * a - d := by congr
    _ = b * a - a * b := by congr
    _ = 0 := by ring
}


/-
We can also handle inequalities using `gcongr` (which stands for “generalized congruence”)
instead of `congr`.
-/

example (a b : ℝ) (h : a ≤ 2*b) : a + b ≤ 3*b := by {
  calc
    a + b ≤ 2*b + b := by gcongr
    _     = 3*b     := by ring
}

/-
The last tactic you will use in computation is the simplifier `simp`. It will
repeatedly apply a number of lemmas that are marked as simplification lemmas.
For instance the proof below simplifies `x - x` to `0` and then `|0|` to `0`.
-/

example (x : ℝ) : |x - x| = 0 := by {
  simp
}


/- ## Universal quantifiers and implications

Let `P` be a predicate on a type `X`. This means for every mathematical
object `x` with type `X`, we get a mathematical statement `P x`.

Lean sees a proof `h` of `∀ x, P x` as a function sending any `x : X` to
a proof `h x` of `P x`.
This already explains the main way to use an assumption or lemma which
starts with a `∀`: we can simply feed it an element of the relevant `X`.

Note we don't need to spell out `X` in the expression `∀ x, P x`
as long as the type of `P` is clear to Lean, which can then infer the type of `x`.

Let's define a predicate to play with `∀`. In that example we have a function
`f : ℝ → ℝ` at hand, and `X = ℝ` (this value of `X` is inferred from the fact
that we feed `x` to `f` which goes from `ℝ` to `ℝ`).
-/

def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

/-
In the above definition, note how there is no parentheses in `f x`.
This is how Lean denotes function application. In `f (-x)` there are parentheses
to prevent Lean from seeing a subtraction of `f` and `x` (which would make no sense).
Also be careful the space between `f` and `(-x)` is mandatory.

The `apply` tactic can be used to specialize universally quantified statements.
-/

example (f : ℝ → ℝ) (hf : even_fun f) : f (-3) = f 3 := by {
  apply hf 3
}

/-
Fortunately, Lean is willing to work for us, so we can leave out the `3` and
let the `apply` tactic compare the goal with the assumption
and decide to specialize it to `x = 3`.
-/

example (f : ℝ → ℝ) (hf : even_fun f) : f (-3) = f 3 := by {
  apply hf
}

/-
In order to prove `∀ x, P x`, we use `intro x₀` to fix an arbitrary object
with type `X`, and call it `x₀` (`intro` stands for “introduce”).
Note we don’t have to use the letter `x₀`, any name will work.

We will prove that the real cosine function is even. After introducing some `x₀`,
the simplifier tactic can finish the proof. Remember to carefully inspect the goal
at the beginning of each line.
-/

open Real in -- this line insists that we mean real cos, not the complex numbers one.
example : even_fun cos := by {
  intro x₀
  simp
}

/-
In the next proof, we introduce the `unfold` tactic, which simply unfolds definitions. Here this
is purely for didactic reason, Lean doesn't need those `unfold` invocations.
-/

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by {
  -- Our assumption on that f is even means ∀ x, f (-x) = f x
  unfold even_fun at hf -- note how `hf` changes after this line
  -- and the same for g
  unfold even_fun at hg
  -- We need to prove ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- Let x₀ be any real number
  intro x₀
  -- and let's compute
  calc
    (f + g) (-x₀) = f (-x₀) + g (-x₀)  := by simp
    _             = f x₀ + g (-x₀)     := by congr 1; apply hf
  -- put you cursor between `;` and `apply` in the previous line to see the intermediate goal
    _             = f x₀ + g x₀        := by congr 1; apply hg
    _             = (f + g) x₀         := by simp
}

/-
You can use the `specialize` tactic to specialize a universally quantified assumption before
using it.
-/

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by {
  -- Let x₀ be any real number
  intro x₀
  specialize hf x₀ -- hf is now only about the x₀ we just introduced
  specialize hg x₀ -- hg is now only about the x₀ we just introduced
  -- and let's compute
  -- (note how `congr` now finds assumptions finishing those steps)
  calc
    (f + g) (-x₀) = f (-x₀) + g (-x₀)  := by simp
    _             = f x₀ + g (-x₀)     := by congr
    _             = f x₀ + g x₀        := by congr
    _             = (f + g) x₀         := by simp
}


/-
Let's now combine the universal quantifier with implication.

In the next definitions, note how `∀ x₁, ∀ x₂, ...` is abbreviated to `∀ x₁ x₂, ...`.
-/

def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

/-
Lean uses a single arrow `→` to denote implication. This is the same arrow as in `f : ℝ → ℝ`.
Indeed Lean sees a proof of the implication `P → Q` as a
function from proofs of `P` to proofs of `Q`.

So an assumption `hf : non_decreasing f` is a function that takes as input two numbers
and a inequality between them and outputs an inequality between their images under `f`.

We can again use `apply` to use the assumption `hf`. This tactic asks for an input that is
either a full proof, or a proof of statement involving universal quantifiers and implications
in front of some statement that can be specialized to the current goal.
-/

example (f : ℝ → ℝ) (hf : non_decreasing f) (x₁ x₂ : ℝ) (hx : x₁ ≤ x₂) : f x₁ ≤ f x₂ := by {
  unfold non_decreasing at hf -- you could skip this line
  apply hf
  apply hx
  -- A one-line proof would be `apply hf x₁ x₂ hx`
}

/- # Finding lemmas

Lean’s mathematical library contains many useful facts, and remembering all of
them by name is infeasible. We already saw the simplifier tactic `simp` which
applies many lemmas without using their names.

The `apply?` tactic will find lemmas from the library and tell you their names.
It creates a suggestion below the goal display. You can click on this suggestion
to edit your code. -/

example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by {
  apply? -- yields `exact Continuous.exists_forall_le_of_hasCompactSupport hf h2f`
}

/- ## Existential quantifiers

In order to prove `∃ x, P x`, we give some `x₀` that works with `use x₀` and
then prove `P x₀`. This `x₀` can be an object from the local context
or a more complicated expression. In the example below, the property
to check after `use` is true by definition so the proof is over.
-/
example : ∃ n : ℕ, 8 = 2*n := by {
  use 4
}

/-
In order to use `h : ∃ x, P x`, we use the `rcases` tactic to fix
one `x₀` that works.

Again `h` can come straight from the local context or can be a more
complicated expression.

-/

example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by {
  rcases h₁ with ⟨k, hk⟩ -- we fix some `k` such that `b = a * k`
  rcases h₂ with ⟨l, hl⟩ -- we fix some `l` such that `c = b * l`
  -- Since `a ∣ c` means `∃ k, c = a*k`, we need the `use` tactic.
  use k*l
  calc
    c = b*l     := by congr
    _ = (a*k)*l := by congr
    _ = a*(k*l) := by ring
}

/-
## Conjunctions

Given two statements `P` and `Q`, the conjunction `P ∧ Q` is the statement that
`P` and `Q` are both true.

In order to prove `P ∧ Q` we use the `constructor` tactic that splits the goal
into proving `P` and then proving `Q`.

In order to use a proof `h` of `P ∧ Q`, we use `h.1` to get a proof of `P`
and `h.2` to get a proof of `Q`. We can also use `rcases h with ⟨hP, hQ⟩` to
get `hP : P` and `hQ : Q`.
-/

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by {
  constructor
  apply h.2
  apply h.1
}

/-
## Limits

Now, let's put everything together to prove a lemma about limits of sequences of real numbers.

Recall that a sequence `u` converges to a limit `l` if the following holds:
def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

Let’s see an example manipulating this definition and using a lot of the tactics
we’ve seen above: if `u` is constant with value `l` then `u` tends to `l`.
 -/
example (h : ∀ n, u n = l) : seq_limit u l := by {
  unfold seq_limit
  intro ε hε
  use 0
  intro n hn
  calc
    |u n - l| = |l - l| := by congr; apply h
    _ = 0 := by simp
    _ ≤ ε := by gcongr
}

/- When dealing with absolute values, we'll use the lemma:

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

When dealing with max, we’ll use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

The way we will use those lemmas is with the rewriting command `rw`. Let's see an example.

Note how we can use `by` anywhere to start proving something using tactics. In the example
below, we use it to prove `ε/2 > 0` from our assumption `ε > 0`.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by {
  intro ε ε_pos
  rcases hu (ε/2) (by apply?) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by apply?) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intro n hn
  rw [ge_max_iff] at hn -- Note how hn changes from `n ≥ max N₁ N₂` to `n ≥ N₁ ∧ n ≥ N₂`
  specialize hN₁ n hn.1
  specialize hN₂ n hn.2
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := by simp
    _ = |(u n - l) + (v n - l')|                      := by congr; ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply?
    _ ≤ ε/2 + ε/2                                     := by gcongr
    _ = ε                                             := by simp
}

end Tutorial

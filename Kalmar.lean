-- This module serves as the root of the `Kalmar` library.
-- Import modules here that should be built as part of the library.
import Kalmar.Basic
import Batteries.Data.List.Basic
import Mathlib.Data.List.Lattice
import Mathlib.Data.List.Nodup
import Init.Data.List.Sublist

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union


abbrev var : Type := Nat

inductive formula where
| atom (v : var) : formula
| neg : formula → formula
| impl : formula → formula → formula
deriving DecidableEq

prefix:51 " ~ " => formula.neg
infixr:50 " ⇒ " => formula.impl

abbrev truth_assignment : Type := var → Bool

def extension (ta : truth_assignment) : formula → Bool
| .atom a => ta a
| .neg A1 => not (extension ta A1)
| .impl A1 A2 =>
    match (extension ta A1), (extension ta A2) with
    | true, false => false
    | _, _        => true

postfix:50 "* " => extension

def satisfies (v : truth_assignment) (A : formula) : Prop :=
  (v*) A = true

infix:50 " ⊨ " => satisfies

def tautology (A : formula) : Prop :=
  ∀ (v : truth_assignment), v ⊨ A

prefix:50 " ⊨ " => tautology

inductive entails : Finset formula → formula → Prop where
| prem (Γ : Finset formula) (A : formula) :    A ∈ Γ → entails Γ A
| ax1 (Γ : Finset formula) (A B : formula) :   entails Γ (A ⇒ (B ⇒ A))
| ax2 (Γ : Finset formula) (A B C : formula) : entails Γ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
| ax3 (Γ : Finset formula) (A B : formula) :   entails Γ ((~A) ⇒ (A ⇒ B))
| ax4 (Γ : Finset formula) (A : formula) :     entails Γ (((~A) ⇒ A) ⇒ A)
| ax5 (Γ : Finset formula) (A B : formula) :   entails Γ (((~B) ⇒ (~A)) ⇒ (((~B) ⇒ A) ⇒ B))
| ax6 (Γ : Finset formula) (A : formula) :     entails Γ (A ⇒ A)
| ax7 (Γ : Finset formula) (B : formula) :     entails Γ (B ⇒ (~(~B)))
| ax8 (Γ : Finset formula) (A B : formula) :   entails Γ (A ⇒ ((~B) ⇒ (~(A ⇒ B))))
| ax9 (Γ : Finset formula) (A B : formula) :   entails Γ ((A ⇒ B) ⇒ (((~A) ⇒ B) ⇒ B))
| mp  (Γ : Finset formula) (A B : formula) :   entails Γ A → entails Γ (A ⇒ B) → entails Γ B

infix:50 " ⊢ " => entails

def provable (A : formula) : Prop := ∅ ⊢ A

prefix:50 " ⊢ " => provable

theorem weakening : (γ ⊢ A) → (γ ⊆ Γ) → (Γ ⊢ A) := by
  intro h h'
  induction h with
  | prem A AinG =>
    exact entails.prem Γ A (Finset.mem_of_subset h' AinG)
  | ax1 A B => exact entails.ax1 Γ A B
  | ax2 A B C => exact entails.ax2 Γ A B C
  | ax3 A B => exact entails.ax3 Γ A B
  | ax4 A => exact entails.ax4 Γ A
  | ax5 A B => exact entails.ax5 Γ A B
  | ax6 A => exact entails.ax6 Γ A
  | ax7 B => exact entails.ax7 Γ B
  | ax8 A B => exact entails.ax8 Γ A B
  | ax9 A B => exact entails.ax9 Γ A B
  | mp A1 B h1 h2 h3 h4 =>
    exact entails.mp Γ A1 B h3 h4

theorem deduction {Γ : Finset formula} {A B : formula} :
  (insert A Γ) ⊢ B ↔ Γ ⊢ (A ⇒ B) := by
  constructor
  intro h
  induction h with
  | prem A1 ih =>
    cases Finset.mem_insert.mp ih with
    | inl h =>
      rw [h]; exact entails.ax6 Γ A
    | inr h =>
      exact entails.mp Γ A1 (A ⇒ A1)
        (entails.prem Γ A1 h)
        (entails.ax1 Γ A1 A)
  | ax1 A1 B1 =>
    exact entails.mp  Γ
      (A1 ⇒ B1 ⇒ A1)
      (A ⇒ A1 ⇒ B1 ⇒ A1)
      (entails.ax1 Γ A1 B1)
      (entails.ax1 Γ (A1 ⇒ B1 ⇒ A1) A)
  | ax2 A1 B1 C1 =>
    exact entails.mp Γ
      ((A1 ⇒ B1 ⇒ C1) ⇒ (A1 ⇒ B1) ⇒ A1 ⇒ C1)
      (A ⇒ (A1 ⇒ B1 ⇒ C1) ⇒ (A1 ⇒ B1) ⇒ A1 ⇒ C1)
      (entails.ax2 Γ A1 B1 C1)
      (entails.ax1 Γ ((A1 ⇒ B1 ⇒ C1) ⇒ (A1 ⇒ B1) ⇒ A1 ⇒ C1) A)
  | ax3 A1 B1 =>
    exact entails.mp Γ
      ((~A1) ⇒ (A1 ⇒ B1))
      (A ⇒ ((~A1) ⇒ (A1 ⇒ B1)))
      (entails.ax3 Γ A1 B1)
      (entails.ax1 Γ ( ~ A1 ⇒ A1 ⇒ B1) A)
  | ax4 A1 =>
    exact entails.mp Γ
      (( ~ A1 ⇒ A1) ⇒ A1)
      (A ⇒ ( ~ A1 ⇒ A1) ⇒ A1)
      (entails.ax4 Γ A1)
      (entails.ax1 Γ (( ~ A1 ⇒ A1) ⇒ A1) A)
  | ax5 A1 B1 =>
    exact entails.mp Γ
      (( ~ B1 ⇒ ~ A1) ⇒ ( ~ B1 ⇒ A1) ⇒ B1)
      (A ⇒ ( ~ B1 ⇒ ~ A1) ⇒ ( ~ B1 ⇒ A1) ⇒ B1)
      (entails.ax5 Γ A1 B1)
      (entails.ax1 Γ _ A)
  | ax6 A1 =>
    exact entails.mp Γ
      (A1 ⇒ A1)
      (A ⇒ A1 ⇒ A1)
      (entails.ax6 Γ A1)
      (entails.ax1 Γ (A1 ⇒ A1) A)
  | ax7 B1 =>
    exact entails.mp Γ
      (B1 ⇒ ~ ~ B1)
      (A ⇒ B1 ⇒ ~ ~ B1)
      (entails.ax7 Γ B1)
      (entails.ax1 Γ (B1 ⇒ ~ ~ B1) A)
  | ax8 A1 B1 =>
    exact entails.mp Γ
      (A1 ⇒ ~ B1 ⇒ ~ (A1 ⇒ B1))
      (A ⇒ A1 ⇒ ~ B1 ⇒ ~ (A1 ⇒ B1))
      (entails.ax8 Γ A1 B1)
      (entails.ax1 Γ _ A)
  | ax9 A1 B1 =>
    exact entails.mp Γ
      ((A1 ⇒ B1) ⇒ ( ~ A1 ⇒ B1) ⇒ B1)
      (A ⇒ (A1 ⇒ B1) ⇒ ( ~ A1 ⇒ B1) ⇒ B1)
      (entails.ax9 Γ A1 B1)
      (entails.ax1 Γ ((A1 ⇒ B1) ⇒ ( ~ A1 ⇒ B1) ⇒ B1) A)
  | mp A1 B1 h1 h2 ih1 ih2 =>
    exact entails.mp Γ (A ⇒ A1) (A ⇒ B1) ih1
      (entails.mp Γ
        (A ⇒ A1 ⇒ B1)
        ((A ⇒ A1) ⇒ A ⇒ B1)
        ih2 (entails.ax2 Γ A A1 B1))
  intro h
  have a := entails.prem (insert A Γ) A (Finset.mem_insert_self A Γ)
  cases h with
  | prem _ h =>
    exact entails.mp (insert A Γ) A B a
      (entails.prem (insert A Γ) (A ⇒ B) (Finset.mem_insert.mpr (Or.inr h)))
  | ax1 _ B =>
    exact entails.mp (insert A Γ) A (B ⇒ A) a
      (entails.ax1 (insert A Γ) A B)
  | ax2 A B C =>
    exact entails.mp (insert (A ⇒ B ⇒ C) Γ) (A ⇒ B ⇒ C) ((A ⇒ B) ⇒ A ⇒ C) a
      (entails.ax2 (insert (A ⇒ B ⇒ C) Γ) A B C)
  | ax3 A B =>
    apply entails.mp (insert ( ~ A) Γ) ( ~ A) (A ⇒ B) a
      (entails.ax3 (insert (~A) Γ) A B)
  | ax4 _ =>
    apply entails.mp (insert ( ~ B ⇒ B) Γ) ( ~ B ⇒ B) B a
      (entails.ax4 (insert ( ~ B ⇒ B) Γ) B)
  | ax5 A B =>
    apply entails.mp (insert ( ~ B ⇒ ~ A) Γ) ( ~ B ⇒ ~ A) (( ~ B ⇒ A) ⇒ B) a
      (entails.ax5 (insert ( ~ B ⇒ ~ A) Γ) A B)
  | ax6 A => exact a
  | ax7 _ =>
    exact entails.mp (insert A Γ) A ( ~ ~ A) a (entails.ax7 (insert A Γ) A)
  | ax8 A B =>
    exact entails.mp (insert A Γ) A ( ~ B ⇒ ~ (A ⇒ B)) a (entails.ax8 (insert A Γ) A B)
  | ax9 A B =>
    exact entails.mp (insert (A ⇒ B) Γ) (A ⇒ B) (( ~ A ⇒ B) ⇒ B) a
      (entails.ax9 (insert (A ⇒ B) Γ) A B)
  | mp A1 B1 h2 h3 =>
    exact entails.mp (insert A Γ) A B a
      (entails.mp (insert A Γ) A1 (A ⇒ B)
        (weakening h2 (Finset.subset_insert A Γ))
        (weakening h3 (Finset.subset_insert A Γ)))

def variables_in : formula → Finset var
| .atom a => {a}
| ~ A1 => variables_in A1
| A1 ⇒ A2 => (variables_in A1) ∪ (variables_in A2)

def aux (v : truth_assignment) (A : formula) : formula :=
  if (v*) A then A else A.neg

theorem klemma (A : formula) (v : truth_assignment) :
  (variables_in A).image ((aux v) ∘ formula.atom) ⊢ aux v A := by
  induction A with
  | atom a =>
    simp [variables_in];
    apply entails.prem {aux v (formula.atom a)} (aux v (formula.atom a))
    apply Finset.mem_singleton.mpr
    rfl
  | neg A1 ih =>
    simp [variables_in]
    cases va1 : (v*) A1
    case true =>
      have h1 : aux v A1 = A1 := by simp [aux, va1]
      have h2 : aux v ( ~ A1) = (~(~A1)) := by
        have h3 : (v* ) ( ~ A1) = false := by simp [extension, va1]
        simp [aux, h3]
      have h3 : (variables_in A1).image ((aux v) ∘ formula.atom) ⊢ (A1 ⇒ (~(~A1))) :=
        entails.ax7 ((variables_in A1).image ((aux v) ∘ formula.atom)) A1
      rw [h1] at ih; rw [h2]; simp at ih h3
      apply entails.mp _ _ _ ih h3
    case false =>
      have h1 : aux v A1 = ~ A1 := by simp [aux, va1]
      have h2 : aux v ( ~ A1) = ( ~ A1) := by
        have h3 : (v* ) ( ~ A1) = true := by simp [extension, va1]
        simp [aux, h3]
      rw [h1] at ih; rw [h2];
      assumption
  | impl A1 A2 ih1 ih2 =>
    cases va1 : (v*) A1
    case true =>
      cases va2 : (v*) A2
      case true =>
        have h1 : aux v A1 = A1 := by simp [aux, va1]
        have h2 : aux v A2 = A2 := by simp [aux, va2]
        have h3 : (v*) (A1 ⇒ A2) = true := by simp [extension, va1, va2]
        have h4 : aux v (A1 ⇒ A2) = (A1 ⇒ A2) := by simp [aux, h3]
        rw [h2] at ih2
        have h5 : ((variables_in (A1 ⇒ A2)).image ((aux v) ∘ formula.atom)) ⊢ A2 := by
          simp [variables_in]
          apply weakening ih2
          apply Finset.image_subset_image
          apply Finset.subset_union_right

        have h6 : ((variables_in (A1 ⇒ A2)).image ((aux v) ∘ formula.atom)) ⊢ (A2 ⇒ (A1 ⇒ A2)) :=
          entails.ax1 ((variables_in (A1 ⇒ A2)).image ((aux v) ∘ formula.atom)) A2 A1
        rw [h4]
        apply entails.mp _ _ _ h5 h6
      case false =>
        have h1 : aux v A1 = A1 := by simp [aux, va1]
        have h2 : aux v A2 = ~ A2 := by simp [aux, va2]
        have h3 : (v*) (A1 ⇒ A2) = false := by simp [extension, va1, va2]
        have h4 : aux v (A1 ⇒ A2) = ~ (A1 ⇒ A2) := by simp [aux, h3]
        rw [h1] at ih1
        rw [h2] at ih2
        rw [h4]
        have h5 : ((variables_in (A1 ⇒ A2)).image ((aux v) ∘ formula.atom)) ⊢ (A1 ⇒ ((~A2) ⇒ (~(A1 ⇒ A2)))) :=
          entails.ax8 ((variables_in (A1 ⇒ A2)).image ((aux v) ∘ formula.atom)) A1 A2
        have h6 : ((variables_in (A1 ⇒ A2)).image ((aux v) ∘ formula.atom)) ⊢ A1 := by
          simp [variables_in]
          apply weakening ih1
          apply Finset.image_subset_image
          apply Finset.subset_union_left
        have h7 : ((variables_in (A1 ⇒ A2)).image ((aux v) ∘ formula.atom)) ⊢ ~ A2 := by
          simp [variables_in]
          apply weakening ih2
          apply Finset.image_subset_image
          apply Finset.subset_union_right
        apply entails.mp _ _ _ h7 (entails.mp _ _ _ h6 h5)
    case false =>
      have h1 : aux v A1 = ~ A1 := by simp [aux, va1]
      have h2 : (v*) (A1 ⇒ A2) = true := by simp [extension, va1]
      have h3 : aux v (A1 ⇒ A2) = (A1 ⇒ A2) := by simp [aux, h2]
      rw [h1] at ih1; rw [h3]
      have h4 : ((variables_in (A1 ⇒ A2)).image ((aux v) ∘ formula.atom)) ⊢ ~ A1 := by
        simp [variables_in]
        apply weakening ih1
        apply Finset.image_subset_image
        apply Finset.subset_union_left
      have h5 : ((variables_in (A1 ⇒ A2)).image ((aux v) ∘ formula.atom)) ⊢ ((~ A1) ⇒ (A1 ⇒ A2)) :=
        entails.ax3 _ A1 A2
      apply entails.mp _ _ _ h4 h5

theorem soundness {A : formula} : ⊢ A → ⊨ A := by
  rw [provable, tautology]
  intro h v
  rw [satisfies]
  induction h with
  | prem => contradiction
  | ax1 A1 B1 =>    simp [extension]; cases ((v* ) A1) <;> simp
  | ax2 A1 B1 C1 => simp [extension]; cases ((v* ) A1) <;> cases ((v* ) B1) <;> simp
  | ax3 A1 B1 =>    simp [extension]; cases ((v* ) A1) <;> simp
  | ax4 A1 =>       simp [extension]; cases ((v* ) A1) <;> simp
  | ax5 A1 B1 =>    simp [extension]; cases ((v* ) A1) <;> cases ((v* ) B1) <;> simp
  | ax6 A1 =>       simp [extension]
  | ax7 B1 =>       simp [extension]
  | ax8 A1 B1 =>    simp [extension]; cases ((v* ) A1) <;> cases ((v* ) B1) <;> simp
  | ax9 A1 B1 =>    simp [extension]; cases ((v* ) A1) <;> cases ((v* ) B1) <;> simp
  | mp A1 B1 h1 h2 h3 h4 =>
    rw [← h4]; simp [extension, h3]; cases (v* ) B1 <;> simp

def true_if (a : var) (v : truth_assignment) (b : var) : Bool :=
  if (b == a) then true else v b

def false_if (a : var) (v : truth_assignment) (b : var) : Bool :=
  if (b == a) then false else v b

theorem lemma1 {A : formula} : ∀ (l : Finset var),
  (∀ (v : truth_assignment), l.image ((aux v) ∘ formula.atom) ⊢ A) → ⊢ A := by
  apply Finset.induction
  case empty =>
    simp; intro h; exact h
  case insert =>
    intro a as nd ih h
    apply ih
    intro v
    let ht := h (true_if a v)
    let hf := h (false_if a v)
    rw [Finset.image_insert, deduction] at ht
    rw [Finset.image_insert, deduction] at hf
    have heqt : Finset.image (aux (true_if a v) ∘ formula.atom) as
      = Finset.image (aux v ∘ formula.atom) as := by
      simp [Finset.image]
      have nd' : a ∉ as.val := nd
      congr 1
      apply Multiset.map_congr
      rfl
      intro x hx
      rw [aux, extension, true_if]
      cases xa : x == a
      · simp; rfl
      · rw [Nat.beq_eq_true_eq] at xa
        rw[xa] at hx
        contradiction
    have heqf : Finset.image (aux (false_if a v) ∘ formula.atom) as
      = Finset.image (aux v ∘ formula.atom) as := by
      simp [Finset.image]
      have nd' : a ∉ as.val := nd
      congr 1
      apply Multiset.map_congr
      rfl
      intro x hx
      rw [aux, extension, false_if]
      cases xa : x == a
      · simp; rfl
      · rw [Nat.beq_eq_true_eq] at xa
        rw[xa] at hx
        contradiction
    simp [aux, extension, true_if, heqt] at ht
    simp [aux, extension, false_if, heqf] at hf
    exact entails.mp (Finset.image (aux v ∘ formula.atom) as) _ A hf
      (entails.mp (Finset.image (aux v ∘ formula.atom) as) _ _ ht
        (entails.ax9 (Finset.image (aux v ∘ formula.atom) as) (formula.atom a) A))

theorem completeness {A : formula} : ⊨ A → ⊢ A := by
  dsimp [tautology, provable]
  intro ta
  apply lemma1 (variables_in A)
  intro v
  have la := klemma A v
  have va := ta v
  rw [satisfies] at va
  simp only [aux, va] at la
  exact la

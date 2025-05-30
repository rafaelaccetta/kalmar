-- This module serves as the root of the `Kalmar` library.
-- Import modules here that should be built as part of the library.
import Kalmar.Basic
import Batteries.Data.List.Basic
import Mathlib.Data.List.Lattice
import Mathlib.Data.List.Nodup
import Init.Data.List.Sublist

abbrev var : Type := Nat

inductive formula where
| atom (v : var) : formula
| neg : formula → formula
| impl : formula → formula → formula

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

inductive entails (Γ : List formula) : formula → Prop where
| prem : ∀ (A : formula),     A ∈ Γ → entails Γ A
| ax1 : ∀ (A B : formula),   entails Γ (A ⇒ (B ⇒ A))
| ax2 : ∀ (A B C : formula), entails Γ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
| ax3 : ∀ (A B : formula),   entails Γ ((~A) ⇒ (A ⇒ B))
| ax4 : ∀ (A : formula),     entails Γ (((~A) ⇒ A) ⇒ A)
| ax5 : ∀ (A B : formula),   entails Γ (((~B) ⇒ (~A)) ⇒ (((~B) ⇒ A) ⇒ B))
| ax6 : ∀ (A : formula),     entails Γ (A ⇒ A)
| ax7 : ∀ (B : formula),     entails Γ (B ⇒ (~(~B)))
| ax8 : ∀ (A B : formula),   entails Γ (A ⇒ ((~B) ⇒ (~(A ⇒ B))))
| ax9 : ∀ (A B : formula),   entails Γ ((A ⇒ B) ⇒ (((~A) ⇒ B) ⇒ B))
| mp  : ∀ (A B : formula),   entails Γ A → entails Γ (A ⇒ B) → entails Γ B

infix:50 " ⊢ " => entails

def provable (A : formula) : Prop := [] ⊢ A

prefix:50 " ⊢ " => provable

theorem entails_subset : (γ ⊢ A) → (γ ⊆ Γ) → (Γ ⊢ A) := by
  intro h h'
  induction h with
  | prem A AinG => exact entails.prem A (List.subset_def.mp h' AinG)
  | ax1 A B => exact entails.ax1 A B
  | ax2 A B C => exact entails.ax2 A B C
  | ax3 A B => exact entails.ax3 A B
  | ax4 A => exact entails.ax4 A
  | ax5 A B => exact entails.ax5 A B
  | ax6 A => exact entails.ax6 A
  | ax7 B => exact entails.ax7 B
  | ax8 A B => exact entails.ax8 A B
  | ax9 A B => exact entails.ax9 A B
  | mp A1 B h1 h2 h3 h4 =>
    exact entails.mp _ _ h3 h4

theorem deduction {Γ : List formula} {A B : formula} :
  (A :: Γ) ⊢ B ↔ Γ ⊢ (A ⇒ B) := by
  constructor
  intro h
  induction h with
  | prem A1 h1 =>
    cases List.mem_cons.mp h1
    case inl h2 =>
      rw [h2]
      apply entails.ax6 A
    case inr h2 =>
      have h3 : Γ ⊢ A1 := entails.prem A1 h2
      have h4 : Γ ⊢  (A1 ⇒ (A ⇒ A1)) := entails.ax1 A1 A
      apply entails.mp _ _ h3 h4
  | ax1 A1 B1 =>
    have h1 : Γ ⊢ (A1 ⇒ (B1 ⇒ A1)) := entails.ax1 A1 B1
    have h2 : Γ ⊢ ((A1 ⇒ (B1 ⇒ A1)) ⇒ (A ⇒ (A1 ⇒ (B1 ⇒ A1)))) :=
      entails.ax1 _ A
    apply entails.mp _ _ h1 h2
  | ax2 A1 B1 C1 =>
    have h1 : Γ ⊢ ((A1 ⇒ (B1 ⇒ C1)) ⇒ ((A1 ⇒ B1) ⇒ (A1 ⇒ C1))) :=
      entails.ax2 A1 B1 C1
    have h2 : Γ ⊢ (((A1 ⇒ (B1 ⇒ C1)) ⇒ ((A1 ⇒ B1) ⇒ (A1 ⇒ C1))) ⇒ (A ⇒ ((A1 ⇒ (B1 ⇒ C1)) ⇒ ((A1 ⇒ B1) ⇒ (A1 ⇒ C1))))) :=
      entails.ax1 _ A
    apply entails.mp _ _ h1 h2
  | ax3 A1 B1 =>
    have h1 : Γ ⊢ ((~A1) ⇒ (A1 ⇒ B1)) := entails.ax3 A1 B1
    have h2 : Γ ⊢ (((~A1) ⇒ (A1 ⇒ B1)) ⇒ (A ⇒ ((~A1) ⇒ (A1 ⇒ B1)))) :=
      entails.ax1 _ A
    apply entails.mp _ _ h1 h2
  | ax4 A1 =>
    have h1 : Γ ⊢ (((~A1) ⇒ A1) ⇒ A1) := entails.ax4 A1
    have h2 : Γ ⊢ ((((~A1) ⇒ A1) ⇒ A1) ⇒ (A ⇒ (((~A1) ⇒ A1) ⇒ A1))) :=
      entails.ax1 _ A
    apply entails.mp _ _ h1 h2
  | ax5 A1 B1 =>
    have h1 : Γ ⊢ (((~B1) ⇒ (~A1)) ⇒ (((~B1) ⇒ A1) ⇒ B1)) := entails.ax5 A1 B1
    have h2 : Γ ⊢ ((((~B1) ⇒ (~A1)) ⇒ (((~B1) ⇒ A1) ⇒ B1)) ⇒ (A ⇒ (((~B1) ⇒ (~A1)) ⇒ (((~B1) ⇒ A1) ⇒ B1)))) :=
      entails.ax1 _ A
    apply entails.mp _ _ h1 h2
  | ax6 A1 =>
    have h1 : Γ ⊢ (A1 ⇒ A1) := entails.ax6 A1
    have h2 : Γ ⊢ ((A1 ⇒ A1) ⇒ (A ⇒ (A1 ⇒ A1))) :=
      entails.ax1 _ A
    apply entails.mp _ _ h1 h2
  | ax7 B1 =>
    have h1 : Γ ⊢ (B1 ⇒ (~(~B1))) := entails.ax7 B1
    have h2 : Γ ⊢ ((B1 ⇒ (~(~B1))) ⇒ (A ⇒ (B1 ⇒ (~(~B1))))) :=
      entails.ax1 _ A
    apply entails.mp _ _ h1 h2
  | ax8 A1 B1 =>
    have h1 : Γ ⊢ (A1 ⇒ ((~B1) ⇒ (~(A1 ⇒ B1)))) := entails.ax8 A1 B1
    have h2 : Γ ⊢ ((A1 ⇒ ((~B1) ⇒ (~(A1 ⇒ B1)))) ⇒ (A ⇒ (A1 ⇒ ((~B1) ⇒ (~(A1 ⇒ B1)))))) :=
      entails.ax1 _ A
    apply entails.mp _ _ h1 h2
  | ax9 A1 B1 =>
    have h1 : Γ ⊢ ((A1 ⇒ B1) ⇒ (((~A1) ⇒ B1) ⇒ B1)) := entails.ax9 A1 B1
    have h2 : Γ ⊢ (((A1 ⇒ B1) ⇒ (((~A1) ⇒ B1) ⇒ B1)) ⇒ (A ⇒ ((A1 ⇒ B1) ⇒ (((~A1) ⇒ B1) ⇒ B1)))) :=
      entails.ax1 _ A
    apply entails.mp _ _ h1 h2
  | mp A1 B1 h1 h2 h3 h4 =>
    have h5 : Γ ⊢ ((A ⇒ (A1 ⇒ B1)) ⇒ ((A ⇒ A1) ⇒ (A ⇒ B1))):= entails.ax2 A A1 B1
    apply entails.mp _ _ h3 (entails.mp _ _ h4 h5)
  intro h
  have h1 : (A :: Γ) ⊢ A := entails.prem A (List.mem_cons_self A Γ)
  cases h with
  | prem _ h2 =>
    have h3 : (A :: Γ) ⊢ (A ⇒ B) := entails.prem (A ⇒ B) (List.mem_cons.mpr (Or.inr h2))
    apply entails.mp _ _ h1 h3
  | ax1 _ B =>
    have h2 : (A :: Γ) ⊢ (A ⇒ (B ⇒ A)) := entails.ax1 A B
    apply entails.mp _ _ h1 h2
  | ax2 A B C =>
    have h2 : ((A ⇒ B ⇒ C) :: Γ) ⊢ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) := entails.ax2 A B C
    apply entails.mp _ _ h1 h2
  | ax3 A B =>
    have h2 : (( ~ A) :: Γ) ⊢ ((~A) ⇒ (A ⇒ B)) := entails.ax3 A B
    apply entails.mp _ _ h1 h2
  | ax4 _ =>
    have h2 : ( ~ B ⇒ B) :: Γ ⊢ (( ~ B ⇒ B) ⇒ B) := entails.ax4 B
    apply entails.mp _ _ h1 h2
  | ax5 A B =>
    have h2 : ( ~ B ⇒ ~ A) :: Γ ⊢ (((~B) ⇒ (~A)) ⇒ (((~B) ⇒ A) ⇒ B)) := entails.ax5 A B
    apply entails.mp _ _ h1 h2
  | ax6 A => apply h1
  | ax7 _ =>
    have h2 : A :: Γ ⊢ (A ⇒ (~ ~ A)) := entails.ax7 A
    apply entails.mp _ _ h1 h2
  | ax8 A B =>
    have h2 : ( A :: Γ) ⊢ (A ⇒ ((~B) ⇒ (~(A ⇒ B)))) := entails.ax8 A B
    apply entails.mp _ _ h1 h2
  | ax9 A B =>
    have h2 : ((A ⇒ B) :: Γ) ⊢ ((A ⇒ B) ⇒ (((~A) ⇒ B) ⇒ B)) := entails.ax9 A B
    apply entails.mp _ _ h1 h2
  | mp A1 _ h2 h3 =>
    have h4 : A :: Γ ⊢ A1 := entails_subset h2 (List.subset_cons_self A Γ)
    have h5 : A :: Γ ⊢ (A1 ⇒ A ⇒ B) := entails_subset h3 (List.subset_cons_self A Γ)
    apply entails.mp _ _ h1 (entails.mp _ _ h4 h5)

def variables_in : formula → List var
| .atom a => [a]
| ~ A1 => variables_in A1
| A1 ⇒ A2 => (variables_in A1) ∪ (variables_in A2)

theorem variables_in_nodup : (A : formula) → (variables_in A).Nodup
  | .atom a => by simp [variables_in]
  | ~ A1 => variables_in_nodup A1
  | A1 ⇒ A2 => List.Nodup.union (variables_in A1) (variables_in_nodup A2)


def aux (v : truth_assignment) (A : formula) : formula :=
  if (v*) A then A else A.neg

theorem klemma (A : formula) (v : truth_assignment) :
  ((variables_in A).map formula.atom).map (aux v) ⊢ aux v A := by
  induction A with
  | atom a =>
    simp [variables_in]; rw [deduction]; apply entails.ax6
  | neg A1 ih =>
    simp [variables_in]
    cases va1 : (v*) A1
    case true =>
      have h1 : aux v A1 = A1 := by simp [aux, va1]
      have h2 : aux v ( ~ A1) = (~(~A1)) := by
        simp [aux]
        have h3 : (v* ) ( ~ A1) = false := by simp [extension, va1]
        simp [h3]
      have h3 : List.map (aux v) ((variables_in A1).map formula.atom) ⊢ (A1 ⇒ (~(~A1))) :=
        entails.ax7 A1
      rw [h1] at ih; rw [h2]; simp at ih h3
      apply entails.mp _ _ ih h3
    case false =>
      have h1 : aux v A1 = ~ A1 := by simp [aux, va1]
      have h2 : aux v ( ~ A1) = ( ~ A1) := by
        simp [aux]
        have h3 : (v* ) ( ~ A1) = true := by simp [extension, va1]
        simp [h3]
      rw [h1] at ih; rw [h2]; simp at ih; assumption
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
        have h5 : List.map (aux v) ((variables_in (A1 ⇒ A2)).map formula.atom) ⊢ (A2 ⇒ (A1 ⇒ A2)) :=
          entails.ax1 A2 A1
        have h6 : (List.map (aux v) ((variables_in (A1 ⇒ A2)).map formula.atom) ⊢ A2) := by
          simp [variables_in]; simp at ih2
          apply entails_subset ih2
          apply List.map_subset
          rw [List.subset_def]
          intro a h
          apply List.mem_union_right
          assumption
        rw [h4]
        apply entails.mp _ _ h6 h5
      case false =>
        have h1 : aux v A1 = A1 := by simp [aux, va1]
        have h2 : aux v A2 = ~ A2 := by simp [aux, va2]
        have h3 : (v*) (A1 ⇒ A2) = false := by simp [extension, va1, va2]
        have h4 : aux v (A1 ⇒ A2) = ~ (A1 ⇒ A2) := by simp [aux, h3]
        rw [h1] at ih1
        rw [h2] at ih2
        rw [h4]
        have h5 : List.map (aux v) ((variables_in (A1 ⇒ A2)).map formula.atom) ⊢ (A1 ⇒ ((~A2) ⇒ (~(A1 ⇒ A2)))) :=
          entails.ax8 A1 A2
        have h6 : List.map (aux v) ((variables_in (A1 ⇒ A2)).map formula.atom) ⊢ A1 := by
          simp [variables_in]; simp at ih1
          apply entails_subset ih1
          apply List.map_subset
          rw [List.subset_def]
          intro a h
          apply List.mem_union_left
          assumption
        have h7 : List.map (aux v) ((variables_in (A1 ⇒ A2)).map formula.atom) ⊢ ~ A2 := by
          simp [variables_in]; simp at ih2
          apply entails_subset ih2
          apply List.map_subset
          rw [List.subset_def]
          intro a h
          apply List.mem_union_right
          assumption
        apply entails.mp _ _ h7 (entails.mp _ _ h6 h5)
    case false =>
      have h1 : aux v A1 = ~ A1 := by simp [aux, va1]
      have h2 : (v*) (A1 ⇒ A2) = true := by simp [extension, va1]
      have h3 : aux v (A1 ⇒ A2) = (A1 ⇒ A2) := by simp [aux, h2]
      rw [h1] at ih1; rw [h3]
      have h4 : List.map (aux v) ((variables_in (A1 ⇒ A2)).map formula.atom) ⊢ ~ A1 := by
        simp [variables_in]; simp at ih1
        apply entails_subset ih1
        apply List.map_subset
        rw [List.subset_def]
        intro a h
        apply List.mem_union_left
        assumption
      have h5 : List.map (aux v) ((variables_in (A1 ⇒ A2)).map formula.atom) ⊢ ((~ A1) ⇒ (A1 ⇒ A2)) :=
        entails.ax3 A1 A2
      apply entails.mp _ _ h4 h5

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
  if (b = a) then true else v b

def false_if (a : var) (v : truth_assignment) (b : var) : Bool :=
  if (b = a) then false else v b

theorem lemma1 {A : formula} {l : List var} (lnd : l.Nodup) :
  (∀ (v : truth_assignment), (List.map (aux v) ((l).map formula.atom)) ⊢ A) → ⊢ A := by
  intro h
  induction l with
  | nil => simp at h; exact h
  | cons head tail ih =>
    apply ih (List.Nodup.of_cons lnd)
    intro v; simp only [List.map] at h
    have hnit := List.Nodup.not_mem lnd; rw [Not] at hnit
    have htit : List.map (aux (true_if head v) ∘ formula.atom) tail = List.map (aux v) (List.map formula.atom tail) := by
      simp; intro a aint
      cases hah : (a == head) <;> simp at hah
      simp [aux, extension, true_if, hah]
      rw [hah] at aint; contradiction
    have hfit : List.map (aux (false_if head v) ∘ formula.atom) tail = List.map (aux v) (List.map formula.atom tail) := by
      simp; intro a aint
      cases hah : (a == head) <;> simp at hah
      simp [aux, extension, false_if, hah]
      rw [hah] at aint; contradiction
    have ht : List.map (aux v) (List.map formula.atom tail) ⊢ ((formula.atom head) ⇒ A) := by
      have hv := h (true_if head v); simp at hv
      rw [htit, deduction] at hv
      have he : aux (true_if head v) (formula.atom head) = formula.atom head := by
        simp [aux, extension, true_if]
      rw [he] at hv; exact hv
    have hf : List.map (aux v) (List.map formula.atom tail) ⊢ ((~(formula.atom head)) ⇒ A) := by
      have hv := h (false_if head v); simp at hv
      rw [hfit, deduction] at hv
      have he : aux (false_if head v) (formula.atom head) = ~(formula.atom head) := by
        simp [aux, extension, false_if]
      rw [he] at hv; exact hv
    have hax9 := @entails.ax9 (List.map (aux v) (List.map formula.atom tail)) (formula.atom head) A
    apply entails.mp _ _ hf (entails.mp _ _ ht hax9)

theorem completeness {A : formula} : ⊨ A → ⊢ A := by
  dsimp [tautology, provable]
  intro ta; apply lemma1 (variables_in_nodup A)
  intro v; have la := klemma A v; have va := ta v
  rw [satisfies] at va; simp only [aux, va] at la; exact la

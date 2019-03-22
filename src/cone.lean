
import linear_algebra.basic
import data.real.basic
import data.set.basic
import tactic.interactive
import .inner_product_space

noncomputable theory
local attribute [instance] classical.prop_decidable

section basic

variables {α : Type*} {β : Type*} {ι : Sort _} 
  [add_comm_group α] [vector_space ℝ α] [add_comm_group β] [vector_space ℝ β] 
  (A : set α) (B : set α) (x : α)  

open set

-- Cones

def cone (A : set α) : Prop :=
  ∀x ∈ A, ∀(c :real), 0 ≤ c → c • x ∈ A

lemma cone_empty : 
  cone ({} : set α) := 
by finish

lemma cone_univ : 
  cone (univ : set α) := 
by finish

lemma cone_inter (hA: cone A) (hB: cone B) : 
  cone (A ∩ B) :=
λ x hx c hc,
  mem_inter (hA _ (mem_of_mem_inter_left  hx) _ hc)
            (hB _ (mem_of_mem_inter_right hx) _ hc)

lemma cone_Inter {s: ι → set α} (h: ∀ i : ι, cone (s i)) : 
  cone (Inter s) :=
by unfold cone; finish

lemma cone_union (hA: cone A) (hB: cone B) : 
  cone (A ∪ B) :=
begin
  intros x hx c hc,
  apply or.elim (mem_or_mem_of_mem_union hx),
  { intro h, 
    apply mem_union_left, 
    apply hA _ h _ hc },
  { intro h, 
    apply mem_union_right,
    apply hB _ h _ hc }
end

lemma cone_Union {s: ι → set α} (h: ∀ i : ι, cone (s i)) : 
  cone (Union s) :=
begin
  intros x hx c hc,
  apply exists.elim (mem_Union.1 hx),
  intros i hi,
  apply mem_Union.2,
  use i,
  apply h i _ hi _ hc
end

lemma cone_subspace {s : subspace ℝ α} : 
  cone (s.carrier) :=
λ x hx c hc, s.smul c hx

lemma cone_contains_0 (hA : cone A) : 
  A ≠ ∅ ↔ (0 : α) ∈ A :=
begin
 apply iff.intro,
 { intros h, 
   apply exists.elim (exists_mem_of_ne_empty h), 
   intros x hx, rw ←zero_smul ℝ, 
   apply hA x hx 0 (le_refl 0) },
 { intros h, 
   exact ne_empty_of_mem h }
end

lemma cone_0 : cone ({0} : set α) :=
begin
  intros x hx c hc,
  apply mem_singleton_of_eq,
  convert smul_zero c,
  exact eq_of_mem_singleton hx
end

open real_inner_product_space

def inner_product_cone (α : Type*) [add_comm_group α] [real_inner_product_space α] : set (α × ℝ) :=
  { x : α × ℝ | real.sqrt ⟪ x.1, x.1 ⟫ ≤ x.2 }

lemma cone_norm_cone {α : Type*} [add_comm_group α] [real_inner_product_space α] : 
cone (inner_product_cone α) :=
begin
  intros x ha c hc,
  unfold inner_product_cone at *,
  simp [inner_self_nonneg, inner_smul_right, inner_smul_left],
  rw [← mul_assoc c c, real.sqrt_mul (mul_self_nonneg _), real.sqrt_mul_self hc],
  apply mul_le_mul (le_refl _),
  apply ha,
  apply real.sqrt_nonneg,
  apply hc
end

end basic

section dual_cone

variables {α : Type*} {β : Type*}
  [add_comm_group α] 
  [add_comm_group β] 
  [real_inner_product_space α] 
  [real_inner_product_space β] 
  (A : set α) (B : set α)

open real_inner_product_space

def dual_cone (A : set α) : set α := { y | ∀ x ∈ A, 0 ≤ ⟪ x , y ⟫ }

lemma cone_dual_cone : cone (dual_cone A) :=
begin
  intros x ha c hc z hz,
  rw inner_smul_right,
  apply zero_le_mul hc,
  exact ha _ hz
end

lemma inner_product_cone_self_dual {α : Type*} [add_comm_group α] [real_inner_product_space α] : 
  dual_cone (inner_product_cone α) = inner_product_cone α :=
begin
  have h_ltr: dual_cone (inner_product_cone α) ⊆ inner_product_cone α,
  begin
    assume (y : α × ℝ) (hy : y ∈ dual_cone (inner_product_cone α)),
    by_cases h_cases : y.fst = 0,
    { 
      have h : 0 ≤ ⟪ (0,1), y ⟫,
      begin
        apply hy,
        unfold inner_product_cone,
        simp [zero_le_one]
      end,
      show y ∈ inner_product_cone α,
      begin
        simp [inner_product_cone, h_cases],
        unfold inner at h,
        simp at h,
        exact h
      end
    },
    { 
      have h : 0 ≤ ⟪ - y.fst, y.fst ⟫ + real.sqrt ⟪ y.fst, y.fst ⟫ * y.snd,
      { 
        apply hy (- y.fst, real.sqrt ⟪ y.fst, y.fst ⟫),
        unfold inner_product_cone,
        simp
      },
      have h : ⟪ y.fst, y.fst ⟫ ≤ real.sqrt ⟪ y.fst, y.fst ⟫ * y.snd,
      { 
        apply le_of_sub_nonneg, 
        rwa [←neg_add_eq_sub, ←inner_neg_left]
      },
      have h : real.sqrt ⟪ y.fst, y.fst ⟫ * ⟪ y.fst, y.fst ⟫ ≤ real.sqrt ⟪ y.fst, y.fst ⟫ * (real.sqrt ⟪ y.fst, y.fst ⟫ * y.snd),
        from mul_le_mul (le_refl _) h (inner_self_nonneg _) (real.sqrt_nonneg _),
      have h : ⟪ y.fst, y.fst ⟫ * real.sqrt ⟪ y.fst, y.fst ⟫ ≤ ⟪ y.fst, y.fst ⟫ * y.snd,
      {
        rw [←mul_assoc, ←real.sqrt_mul (inner_self_nonneg _), real.sqrt_mul_self (inner_self_nonneg _)] at h,
        rwa mul_comm
      },
      show y ∈ inner_product_cone α,
        from le_of_mul_le_mul_left h (inner_self_pos h_cases)
    }
  end,
  have h_rtl: inner_product_cone α ⊆ dual_cone (inner_product_cone α),
  begin
    assume (y : α × ℝ) (hy : real.sqrt ⟪ y.1, y.1 ⟫ ≤ y.2),
    assume (x : α × ℝ) (hx :  real.sqrt ⟪ x.1, x.1 ⟫ ≤ x.2),
    have hx' : real.sqrt ⟪ - x.1, - x.1 ⟫ ≤ x.2,
      by simpa,
    have h : ⟪ -x.1, y.1 ⟫ ≤ x.2 * y.2,
      calc ⟪ -x.1, y.1 ⟫ ≤ real.sqrt ⟪ -x.1, -x.1 ⟫ * real.sqrt ⟪ y.1, y.1 ⟫ : ip_cauchy_schwartz' _ _
                    ... ≤ x.2 * y.2                                         : mul_le_mul hx' hy (real.sqrt_nonneg _) (le_trans (real.sqrt_nonneg _) hx'),
    show 0 ≤ ⟪ x.fst, y.fst ⟫ + x.snd * y.snd,
    {
      rw [inner_neg_left] at h,
      rw add_comm,
      convert sub_nonneg_of_le h,
      simp
    }
  end,
  show dual_cone (inner_product_cone α) = inner_product_cone α,
    from set.subset.antisymm h_ltr h_rtl
end

end dual_cone

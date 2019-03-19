import analysis.normed_space.basic
import algebra.module
import algebra.pi_instances
import data.real.basic
import data.complex.basic
import data.set.basic
import data.set.intervals
import tactic.interactive
import tactic.linarith
import linear_algebra.basic
import ring_theory.algebra


--TODO: move
lemma image_neg_Iio (r : ℝ) : image (λz, -z) {z : ℝ | z < r} = {z : ℝ | -r < z} :=
begin
  apply set.ext,
  intros z,
  apply iff.intro,
  { intros hz,
    apply exists.elim hz,
    intros z' hz',
    rw [←hz'.2],
    simp at *,
    exact hz'.1 },
  { intros hz, 
    simp at *,
    use -z,
    simp [hz], 
    exact neg_lt.1 hz }
end

--TODO: move
lemma image_neg_Iic (r : ℝ) : image (λz, -z) {z : ℝ | z ≤ r} = {z : ℝ | -r ≤ z} :=
begin
  apply set.ext,
  intros z,
  apply iff.intro,
  { intros hz,
    apply exists.elim hz,
    intros z' hz',
    rw [←hz'.2],
    simp at *,
    exact hz'.1 },
  { intros hz, 
    simp at *,
    use -z,
    simp [hz], 
    exact neg_le.1 hz }
end

--TODO: move
lemma is_linear_map_neg {α R : Type*} [add_comm_group α] [ring R] [module R α]: 
  is_linear_map R (λ (z : α), -z) :=
is_linear_map.mk neg_add (λ x y, (smul_neg x y).symm)

--TODO: move
lemma is_linear_map_add {α R : Type*} [add_comm_group α] [ring R] [module R α]: 
  is_linear_map R (λ (x : α × α), x.1 + x.2) :=
begin
  apply is_linear_map.mk,
  { intros x y,
    simp },
  { intros x y,
    simp [smul_add] }
end

--TODO: move
lemma is_linear_map_sub {α R : Type*} [add_comm_group α] [ring R] [module R α]: 
  is_linear_map R (λ (x : α × α), x.1 - x.2) :=
begin
  apply is_linear_map.mk,
  { intros x y,
    simp },
  { intros x y,
    simp [smul_add] }
end

--TODO: move
lemma is_linear_map_smul {α R : Type*} [add_comm_group α] [comm_ring R] [module R α] (c : R): 
  is_linear_map R (λ (z : α), c • z) :=
begin
  refine is_linear_map.mk (smul_add c) _,
  intros _ _,
  simp [smul_smul],
  ac_refl
end

section

variables {α : Type*} {β : Type*} {ι : Sort _} 
  [add_comm_group α] [vector_space ℝ α] [add_comm_group β] [vector_space ℝ β] 
  (A : set α) (B : set α) (x : α)  

open set

/-- Convexity of sets -/
def convex (A : set α) := 
∀ (x y : α) (a b : ℝ), x ∈ A → y ∈ A → 0 ≤ a → 0 ≤ b → a + b = 1 → 
a • x  + b • y ∈ A

/-- Alternative definition of set convexity -/
lemma convex_iff: 
  convex A ↔ ∀ {x y : α} {θ : ℝ}, 
    x ∈ A → y ∈ A → 0 ≤ θ → θ ≤ 1 → θ • x  + (1 - θ) • y ∈ A := 
⟨
  begin 
    assume h x y θ hx hy hθ₁ hθ₂, 
    have hθ₂: 0 ≤ 1 - θ, by linarith,
    exact (h _ _ _ _ hx hy hθ₁ hθ₂ (by linarith)) 
  end,
  begin
    assume h x y a b hx hy ha hb hab, 
    have ha': a ≤ 1, by linarith,
    have hb': b = 1 - a, by linarith,
    rw hb',
    exact (h hx hy ha ha')
  end
⟩ 

/-- Another alternative definition of set convexity -/
lemma convex_iff_div: 
  convex A ↔ ∀ {x y : α} {a : ℝ} {b : ℝ}, 
    x ∈ A → y ∈ A → 0 ≤ a → 0 ≤ b → 0 < a + b → (a/(a+b)) • x  + (b/(a+b)) • y ∈ A :=
⟨
  begin
    assume h x y a b hx hy ha hb hab, 
    apply h _ _ _ _ hx hy,
    have ha', from mul_le_mul_of_nonneg_left ha (le_of_lt (inv_pos hab)),
    rwa [mul_zero, ←div_eq_inv_mul] at ha',
    have hb', from mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos hab)),
    rwa [mul_zero, ←div_eq_inv_mul] at hb',
    rw [←add_div],
    exact div_self (ne_of_lt hab).symm
    end,
    begin
    assume h x y a b hx hy ha hb hab, 
    have h', from h hx hy ha hb,
    rw [hab, div_one, div_one] at h',
    exact h' zero_lt_one
  end
⟩ 

local notation `I` := (Icc 0 1 : set ℝ)

/-- Segments in a vector space -/
def segment (x y : α) := {z : α | ∃ l : ℝ, l ∈ I ∧ z - x = l•(y-x)}
local notation `[`x `, ` y `]` := segment x y

lemma left_mem_segment (x y : α) : x ∈ [x, y] := ⟨0, ⟨⟨le_refl _, zero_le_one⟩, by simp⟩⟩
lemma right_mem_segment (x y : α) : y ∈ [x, y] := ⟨1, ⟨⟨zero_le_one, le_refl _⟩, by simp⟩⟩

lemma mem_segment_iff {x y z : α} : z ∈ [x, y] ↔ ∃ l ∈ I, z = x + l•(y - x) :=
by split ; rintro ⟨l, l_in, H⟩ ; use [l, l_in] ; try { rw sub_eq_iff_eq_add at H } ; rw H ; abel

lemma mem_segment_iff' {x y z : α} : z ∈ [x, y] ↔ ∃ l ∈ I, z = ((1:ℝ)-l)•x + l•y :=
begin
  split ; rintro ⟨l, l_in, H⟩ ; use [l, l_in] ; try { rw sub_eq_iff_eq_add at H } ; rw H ;
  simp only [smul_sub, sub_smul, one_smul] ; abel,
end

lemma segment_symm (x y : α) : [x, y] = [y, x] :=
begin
  ext z,
  rw [mem_segment_iff', mem_segment_iff'],
  split,
  all_goals {
    rintro ⟨l, ⟨hl₀, hl₁⟩, h⟩,
    use (1-l),
    split,
    split ; linarith,
    rw [h] ; simp },
end

lemma segment_eq_Icc {a b : ℝ} (h : a ≤ b) : [a, b] = Icc a b :=
begin
  ext z,
  rw mem_segment_iff,
  split,
  { rintro ⟨l, ⟨hl₀, hl₁⟩, H⟩,
    rw smul_eq_mul at H,
    have hba : 0 ≤ b - a, by linarith,
    split ; rw H,
    { have := mul_le_mul (le_refl l) hba (le_refl _) hl₀,
      simpa using this, },
    { have := mul_le_mul hl₁ (le_refl (b-a)) hba zero_le_one,
      rw one_mul at this,
      apply le_trans (add_le_add (le_refl a) this),
      convert le_refl _,
      show b = a + (b-a), by ring } },
  { rintro ⟨hza, hzb⟩,
    by_cases hba : b-a = 0,
    { use [(0:ℝ), ⟨le_refl 0, zero_le_one⟩],
      rw zero_smul, linarith },
    { have : (z-a)/(b-a) ∈ I,
      { change b -a ≠ 0 at hba,
        have : 0 < b - a, from lt_of_le_of_ne (by linarith) hba.symm,
        split,
        apply div_nonneg ; linarith,
        apply (div_le_iff this).2,
        simp, convert hzb, ring},
      use [(z-a)/(b-a), this],
      rw [smul_eq_mul, div_mul_cancel],
      ring,
      exact hba}}
end

/-- Alternative defintion of set convexity using segments -/
lemma convex_segment_iff : convex A ↔ ∀ x y ∈ A, [x, y] ⊆ A :=
begin
  apply iff.intro,
  { intros hA x y hx hy z hseg,
    apply exists.elim hseg,
    intros l hl,
    have hz : z = l • y + (1-l) • x,
    begin
      rw sub_eq_iff_eq_add.1 hl.2, 
      rw [smul_sub, sub_smul, one_smul],
      simp
    end,
    rw hz,
    apply (convex_iff A).1 hA hy hx hl.1.1 hl.1.2 },
  { intros hA, 
    rw convex_iff, 
    intros x y θ hx hy hθ₀ hθ₁,
    apply hA y x hy hx,
    use θ,
    apply and.intro,
    { exact and.intro hθ₀ hθ₁ },
    { simp only [smul_sub, sub_smul, one_smul], 
      simp } }
end


/- Examples of convex sets -/

lemma convex_empty : convex (∅ : set α) :=  by finish

lemma convex_singleton (a : α) : convex ({a} : set α) := 
begin 
  intros x y a b hx hy ha hb hab, 
  rw set.eq_of_mem_singleton hx,
  rw set.eq_of_mem_singleton hy,
  rw [←add_smul, hab],
  simp
end

lemma convex_univ : convex (set.univ : set α) := by finish 

lemma convex_inter (hA: convex A) (hB: convex B) : convex (A ∩ B) :=
λ x y a b (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1), 
  ⟨hA _ _ _ _ hx.left hy.left ha hb hab, hB _ _ _ _ hx.right hy.right ha hb hab⟩

lemma convex_Inter {s: ι → set α} (h: ∀ i : ι, convex (s i)) : convex (Inter s) :=
begin
  intros x y a b hx hy ha hb hab,
  apply mem_Inter.2,
  intro i,
  exact h i _ _ _ _ (mem_Inter.1 hx i) (mem_Inter.1 hy i) ha hb hab
end

lemma convex_prod {A : set α} {B : set β} (hA : convex A) (hB : convex B) : 
convex (set.prod A B) :=
begin
  intros x y a b hx hy ha hb hab,
  apply mem_prod.2,
  exact ⟨hA _ _ _ _ (mem_prod.1 hx).1 (mem_prod.1 hy).1 ha hb hab,
        hB _ _ _ _ (mem_prod.1 hx).2 (mem_prod.1 hy).2 ha hb hab⟩
end

lemma convex_linear_image (f : α → β) (hf : is_linear_map ℝ f) (hA : convex A) : convex (image f A) :=
begin
  intros x y a b hx hy ha hb hab,
  apply exists.elim hx, 
  intros x' hx',
  apply exists.elim hy, 
  intros y' hy', 
  use a • x' + b • y',
  apply and.intro,
  { apply hA _ _ _ _ hx'.1 hy'.1 ha hb hab },
  { simp [hx',hy',hf.add,hf.smul] }
end 

lemma convex_linear_image' (f : α →ₗ[ℝ] β) (hA : convex A) : convex (image f A) := 
 convex_linear_image A f.to_fun (linear_map.is_linear f) hA

lemma convex_linear_preimage (A : set β) (f : α → β) (hf : is_linear_map ℝ f) (hA : convex A) : 
  convex (preimage f A) :=
begin
  intros x y a b hx hy ha hb hab,
  simp [hf.add, hf.smul],
  exact hA (f x) (f y) a b hx hy ha hb hab
end 

lemma convex_linear_preimage' (A : set β) (f : α →ₗ[ℝ] β) (hA : convex A) : 
  convex (preimage f A) :=
convex_linear_preimage A f.to_fun (linear_map.is_linear f) hA

lemma convex_Iio (r : ℝ) : convex {z : ℝ | z < r} :=
begin 
  intros x y a b hx hy ha hb hab,
  wlog h : x ≤ y using [x y a b, y x b a],
  exact le_total _ _,
  calc 
    a * x + b * y ≤ a * y + b * y : add_le_add_right (mul_le_mul_of_nonneg_left h ha) _
    ...           = y             : by rw [←add_mul a b y, hab, one_mul]
    ... < r                       : hy
end 

lemma convex_Iic (r : ℝ) : convex {z : ℝ | z ≤ r} :=
begin 
  intros x y a b hx hy ha hb hab,
  wlog h : x ≤ y using [x y a b, y x b a],
  exact le_total _ _,
  calc 
    a * x + b * y ≤ a * y + b * y : add_le_add_right (mul_le_mul_of_nonneg_left h ha) _
    ...           = y             : by rw [←add_mul a b y, hab, one_mul]
    ... ≤ r                       : hy
end 

lemma convex_neg : convex A → convex ((λ z, -z) '' A) := 
convex_linear_image _ _ is_linear_map_neg

lemma convex_neg_preimage : convex A → convex ((λ z, -z) ⁻¹' A) := 
convex_linear_preimage _ _ is_linear_map_neg

lemma convex_smul (c : ℝ): 
  convex A → convex ((λ z, c • z) '' A) := 
convex_linear_image _ _ (is_linear_map_smul c)

lemma convex_smul_preimage (c : ℝ): 
  convex A → convex ((λ z, c • z) ⁻¹' A) := 
convex_linear_preimage _ _ (is_linear_map_smul _)

lemma convex_add : convex A → convex B → convex ((λx : α × α, x.1 + x.2) '' (set.prod A B)) := 
begin
  intros hA hB,
  apply convex_linear_image (set.prod A B) (λx : α × α, x.1 + x.2) is_linear_map_add,
  exact convex_prod hA hB
end

lemma convex_sub : convex A → convex B → convex ((λx : α × α, x.1 - x.2) '' (set.prod A B)) := 
begin
  intros hA hB,
  apply convex_linear_image (set.prod A B) (λx : α × α, x.1 - x.2) is_linear_map_sub,
  exact convex_prod hA hB
end

lemma convex_translation (z : α) (hA : convex A) : convex ((λx, z + x) '' A) :=
begin
  have h : convex ((λ (x : α × α), x.fst + x.snd) '' set.prod (insert z ∅) A),
    from convex_add {z} A (convex_singleton z) hA,
  show convex ((λx, z + x) '' A),
  begin
    rw [@insert_prod _ _ z ∅ A, set.empty_prod, set.union_empty, ←image_comp] at h,
    simp at h,
    exact h
  end
end

lemma convex_affinity (z : α) (c : ℝ) (hA : convex A) : convex ((λx, z + c • x) '' A) :=
begin
  have h : convex ((λ (x : α), z + x) '' ((λ (z : α), c • z) '' A)),
    from convex_translation _ z (convex_smul A c hA),
  show convex ((λx, z + c • x) '' A),
  begin
    rw [←image_comp] at h, 
    simp at h, 
    exact h
  end
end

lemma convex_Ioi (r : ℝ) : convex {z : ℝ | r < z} :=
begin
  rw [← neg_neg r],
  rw (image_neg_Iio (-r)).symm,
  unfold convex,
  intros x y a b hx hy ha hb hab,
  exact convex_linear_image _ _ is_linear_map_neg (convex_Iio (-r)) _ _ _ _ hx hy ha hb hab
end

lemma convex_Ici (r : ℝ) : convex {z : ℝ | r ≤ z} :=
begin
  rw [← neg_neg r],
  rw (image_neg_Iic (-r)).symm,
  unfold convex,
  intros x y a b hx hy ha hb hab,
  exact convex_linear_image _ _ is_linear_map_neg (convex_Iic (-r)) _ _ _ _ hx hy ha hb hab
end

lemma convex_Ioo (r : ℝ) (s : ℝ) : convex (Ioo r s) := 
begin
 apply convex_inter,
 apply convex_Ioi,
 apply convex_Iio,
end

-- TODO: more variants
lemma convex_Ico (r : ℝ) (s : ℝ) : convex (Ico r s) := 
begin
 apply convex_inter,
 apply convex_Ici,
 apply convex_Iio,
end

lemma convex_Icc (r : ℝ) (s : ℝ) : convex (Icc r s) := 
begin
 apply convex_inter,
 apply convex_Ici,
 apply convex_Iic,
end

--lemma convex_halfspace_lt (f : α →ₗ[ℝ] ℝ) (r : ℝ) : 
--  convex {w | f w < r} :=
--begin
--  assume x y a b hx hy ha hb hab,
--  simp,
--  apply convex_Iio _ hx hy ha hb hab
--end

-- TODO: more variants > <= >=, or even in Ioo, Icc etc
lemma convex_halfspace_lt (f : α → ℝ) (h : is_linear_map ℝ f) (r : ℝ) : 
  convex {w | f w < r} :=
begin
  assume x y a b hx hy ha hb hab,
  simp,
  rw [is_linear_map.add ℝ f,  is_linear_map.smul f a,  is_linear_map.smul f b],
  apply convex_Iio _ _ _ _ _ hx hy ha hb hab
end

lemma convex_halfplane (f : α → ℝ) (h : is_linear_map ℝ f) (r : ℝ) : 
  convex {w | f w = r} :=
begin
  assume x y a b hx hy ha hb hab,
  simp at *,
  rw [is_linear_map.add ℝ f,  is_linear_map.smul f a,  is_linear_map.smul f b],
  rw [hx, hy, (add_smul a b r).symm, hab, one_smul]
end

-- TODO: move
instance algebra_complex : algebra ℝ ℂ :=
algebra.of_ring_hom coe $ by constructor; intros; simp [complex.one_re]

-- TODO: move
instance : has_scalar ℝ ℂ := { smul := λ r c, ↑r * c}

--TODO: move
lemma smul_re: ∀ (c : ℝ) (x : ℂ), (c • x).re = c • x.re := 
begin 
  unfold has_scalar.smul, 
  assume _ _,
  rw [complex.mul_re,complex.of_real_im],
  simp
end
  
-- TODO: 
-- TODO: more variants: <=, >=, >, im
lemma convex_halfspace_re_lt (r : ℝ): convex {c : ℂ | c.re < r} :=
by apply convex_halfspace_lt _ (is_linear_map.mk complex.add_re smul_re)

lemma convex_sum {γ : Type*} [decidable_eq γ] (hA : convex A) (z : γ → α) (s : finset γ) :
∀ a : γ → ℝ, s.sum a = 1 → (∀ i ∈ s, 0 ≤ a i) → (∀ i ∈ s, z i ∈ A) → s.sum (λi, a i • z i) ∈ A :=
begin
refine finset.induction _ _ s,
{ intros _ h_sum,
  simp at h_sum,
  exact false.elim h_sum },
{ intros k s hks ih a h_sum ha hz, 
  by_cases h_cases : s.sum a = 0,
  { have hak : a k = 1,
      by rwa [finset.sum_insert hks, h_cases, add_zero] at h_sum,
    have ha': ∀ i ∈ s, 0 ≤ a i,
      from λ i hi, ha i (finset.mem_insert_of_mem hi),
    have h_a0: ∀ i ∈ s, a i = 0,
      from (finset.sum_eq_zero_iff_of_nonneg ha').1 h_cases,
    have h_az0: ∀ i ∈ s, a i • z i = 0,
    begin 
      intros i hi, 
      rw h_a0 i hi, 
      exact zero_smul _ (z i)
    end,
    show finset.sum (insert k s) (λ (i : γ), a i • z i) ∈ A,
    begin
      rw [finset.sum_insert hks, hak, finset.sum_eq_zero h_az0], 
      simp, 
      exact hz k (finset.mem_insert_self k s)
    end },
  { have h_sum_nonneg : 0 ≤ s.sum a ,  
    begin 
      apply finset.zero_le_sum',
      intros i hi,
      apply ha _ (finset.mem_insert_of_mem hi)
    end,
    have h_div_in_A: s.sum (λ (i : γ), ((s.sum a)⁻¹ * a i) • z i) ∈ A, 
    begin 
      apply ih, 
      { rw finset.mul_sum.symm,  
        exact division_ring.inv_mul_cancel h_cases },
      { intros i hi, 
        exact zero_le_mul (inv_nonneg.2 h_sum_nonneg) (ha i (finset.mem_insert_of_mem hi))},
      { intros i hi,
        exact hz i (finset.mem_insert_of_mem hi) } 
    end, 
    have h_sum_in_A: a k • z k 
      + finset.sum s a • finset.sum s (λ (i : γ), ((finset.sum s a)⁻¹ * a i) • z i)
      ∈ A,
    begin
      apply hA, 
      exact hz k (finset.mem_insert_self k s),
      exact h_div_in_A,
      exact ha k (finset.mem_insert_self k s),
      exact h_sum_nonneg,
      rw (finset.sum_insert hks).symm,
      exact h_sum
    end,
    show finset.sum (insert k s) (λ (i : γ), a i • z i) ∈ A,
    begin
      rw finset.sum_insert hks,
      rw finset.smul_sum at h_sum_in_A,
      simp [smul_smul, (mul_assoc (s.sum a) _ _).symm] at h_sum_in_A,
      conv
      begin
        congr,
        congr,
        skip,
        congr, skip, funext,
        rw (one_mul (a _)).symm,
        rw (field.mul_inv_cancel h_cases).symm,
      end,
      exact h_sum_in_A
    end }
}
end

lemma convex_sum_equiv [decidable_eq α]:
  convex A ↔ 
    (∀ (s : finset α) (as : α → ℝ), 
      s.sum as = 1 → (∀ i ∈ s, 0 ≤ as i) → (∀ x ∈ s, x ∈ A) → s.sum (λx, as x • x) ∈ A ) :=
begin
  apply iff.intro,
  { intros hA s as h_sum has hs, 
    exact convex_sum A hA id s _ h_sum has hs },
  { intros h,
    intros x y a b hx hy ha hb hab,
    by_cases h_cases: x = y,
    { rw [h_cases, ←add_smul, hab, one_smul], exact hy },
    { 
    let s := insert x (finset.singleton y),
    have h_sum_eq_add : finset.sum s (λ z, ite (x = z) a b • z) = a • x + b • y,
    begin 
      rw [finset.sum_insert (finset.not_mem_singleton.2 h_cases), 
      finset.sum_singleton],  
      simp [h_cases]
    end,
    rw h_sum_eq_add.symm,
    apply h s,
    { rw [finset.sum_insert (finset.not_mem_singleton.2 h_cases), 
      finset.sum_singleton],
      simp [h_cases], 
      exact hab },
    { intros k hk,
      by_cases h_cases : x = k,
      { simp [h_cases], exact ha },
      { simp [h_cases], exact hb } },
    { intros z hz,
      apply or.elim (finset.mem_insert.1 hz),
      { intros h_eq, rw h_eq, exact hx },
      { intros h_eq, rw finset.mem_singleton at h_eq, rw h_eq, exact hy } } }
  }
end

-- Convex functions

variables (D: set α) (D': set α) (f : α → ℝ) (g : α → ℝ)

def convex_on (f : α → ℝ) : Prop := 
  convex D ∧
  ∀ (x y : α) (a b : ℝ), x ∈ D → y ∈ D → 0 ≤ a → 0 ≤ b → a + b = 1 → 
    f (a • x + b • y) ≤ a * f x + b * f y

-- TODO: do we need a lemma that just repeats the def?

lemma convex_on_alt: 
  convex_on D f ↔ convex D ∧ ∀ {x y : α} {θ : ℝ}, 
    x ∈ D → y ∈ D → 0 ≤ θ → θ ≤ 1 → f (θ • x + (1 - θ) • y) ≤ θ * f x + (1 - θ) * f y := 
⟨
  begin 
    intro h,
    apply and.intro h.1,
    intros x y θ hx hy hθ₁ hθ₂, 
    have hθ₂: 0 ≤ 1 - θ, by linarith,
    exact (h.2 _ _ _ _ hx hy hθ₁ hθ₂ (by linarith)) 
  end,
  begin
    intro h,
    apply and.intro h.1,
    assume x y a b hx hy ha hb hab, 
    have ha': a ≤ 1, by linarith,
    have hb': b = 1 - a, by linarith,
    rw hb',
    exact (h.2 hx hy ha ha')
  end
⟩ 

lemma convex_on_alt2: 
  convex_on D f ↔ convex D ∧ ∀ {x y : α} {a : ℝ} {b : ℝ}, 
    x ∈ D → y ∈ D → 0 ≤ a → 0 ≤ b → 0 < a + b → 
    f ((a/(a+b)) • x + (b/(a+b)) • y) ≤ (a/(a+b)) * f x + (b/(a+b)) * f y :=
⟨
  begin
    intro h,
    apply and.intro h.1,
    intros x y a b hx hy ha hb hab, 
    apply h.2 _ _ _ _ hx hy,
    have ha', from mul_le_mul_of_nonneg_left ha (le_of_lt (inv_pos hab)),
    rwa [mul_zero, ←div_eq_inv_mul] at ha',
    have hb', from mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos hab)),
    rwa [mul_zero, ←div_eq_inv_mul] at hb',
    rw [←add_div],
    exact div_self (ne_of_lt hab).symm
    end,
    begin
    intro h,
    apply and.intro h.1,
    intros x y a b hx hy ha hb hab, 
    have h', from h.2 hx hy ha hb,
    rw [hab, div_one, div_one] at h',
    exact h' zero_lt_one
  end
⟩ 

lemma convex_on_sum {γ : Type} [hγ : decidable_eq γ] (s : finset γ) (z : γ → α) (hs : s ≠ ∅):
  ∀ (a : γ → ℝ), convex_on D f → (∀ i ∈ s, 0 ≤ a i) → (∀ i ∈ s, z i ∈ D) → s.sum a = 1 →
  f (s.sum (λi, a i • z i)) ≤ s.sum (λi, a i • f (z i)) :=
begin
  refine finset.induction (by simp) _ s,
  intros k s hks ih a hf ha hz h_sum,
  by_cases h_cases : s.sum a = 0,
  { have hak : a k = 1,
      by rwa [finset.sum_insert hks, h_cases, add_zero] at h_sum,
    have ha': ∀ i ∈ s, 0 ≤ a i,
      from λ i hi, ha i (finset.mem_insert_of_mem hi),
    have h_a0: ∀ i ∈ s, a i = 0,
      from (finset.sum_eq_zero_iff_of_nonneg ha').1 h_cases,
    have h_az0: ∀ i ∈ s, a i • z i = 0,
    begin 
      intros i hi, 
      rw h_a0 i hi, 
      exact zero_smul _ _
    end,
    have h_afz0: ∀ i ∈ s, a i • f (z i) = 0,
    begin 
      intros i hi, 
      rw h_a0 i hi, 
      exact zero_smul _ _
    end,
    show f (finset.sum (insert k s) (λi, a i • z i)) ≤ finset.sum (insert k s) (λi, a i • f (z i)),
    begin
      rw [finset.sum_insert hks, hak, finset.sum_eq_zero h_az0], 
      rw [finset.sum_insert hks, hak, finset.sum_eq_zero h_afz0], 
      simp
    end },
  { have h_sum_nonneg : 0 ≤ s.sum a ,  
    begin 
      apply finset.zero_le_sum',
      intros i hi,
      apply ha _ (finset.mem_insert_of_mem hi)
    end,
    have ih_div: f (s.sum (λ (i : γ), ((s.sum a)⁻¹ * a i) • z i))
                  ≤ s.sum (λ (i : γ), ((s.sum a)⁻¹ * a i) • f (z i)),
    begin 
      apply ih _ hf,
      { intros i hi, 
        exact zero_le_mul (inv_nonneg.2 h_sum_nonneg) (ha i (finset.mem_insert_of_mem hi))},
      { intros i hi, 
        exact hz i (finset.mem_insert_of_mem hi) },
      { rw finset.mul_sum.symm,  
        exact division_ring.inv_mul_cancel h_cases }
    end, 
    have h_div_in_D: s.sum (λ (i : γ), ((s.sum a)⁻¹ * a i) • z i) ∈ D, 
    begin 
      apply convex_sum _ hf.1, 
      { rw finset.mul_sum.symm,  
        exact division_ring.inv_mul_cancel h_cases },
      { intros i hi, 
        exact zero_le_mul (inv_nonneg.2 h_sum_nonneg) (ha i (finset.mem_insert_of_mem hi))},
      { intros i hi,
        exact hz i (finset.mem_insert_of_mem hi) },
      { exact hγ }
    end, 
    have hf': f (a k • z k     + s.sum a •    s.sum (λ (i : γ), ((finset.sum s a)⁻¹ * a i) • z i))
                   ≤ a k • f (z k) + s.sum a • f (s.sum (λ (i : γ), ((finset.sum s a)⁻¹ * a i) • z i)),
    begin
      apply hf.2, 
      exact hz k (finset.mem_insert_self k s),
      exact h_div_in_D,
      exact ha k (finset.mem_insert_self k s),
      exact h_sum_nonneg,
      rw (finset.sum_insert hks).symm,
      exact h_sum
    end,
    have ih_div': f (a k • z k     + s.sum a • s.sum (λ (i : γ), ((finset.sum s a)⁻¹ * a i) • z i))
                   ≤ a k • f (z k) + s.sum a • s.sum (λ (i : γ), ((finset.sum s a)⁻¹ * a i) • f (z i)),
      from trans hf' (add_le_add_left (mul_le_mul_of_nonneg_left ih_div h_sum_nonneg) _),
    show f (finset.sum (insert k s) (λ (i : γ), a i • z i)) 
          ≤ finset.sum (insert k s) (λ (i : γ), a i • f (z i)),
    begin
      simp [finset.sum_insert hks],
      simp [finset.smul_sum] at ih_div',
      simp [smul_smul, (mul_assoc (s.sum a) _ _).symm] at ih_div',
      convert ih_div',
      repeat { apply funext,
        intro i,
        rw [field.mul_inv_cancel, one_mul],
        exact h_cases }
    end }
end

lemma convex_on_linorder [hα : linear_order α] (f : α → ℝ) : convex_on D f ↔
  convex D ∧ ∀ (x y : α) (a b : ℝ), x ∈ D → y ∈ D → x < y → a ≥ 0 → b ≥ 0 → a + b = 1 → 
    f (a • x + b • y) ≤ a * f x + b * f y :=
begin
  apply iff.intro,
  { intro h,
    apply and.intro h.1,
    intros x y a b hx hy hxy ha hb hab, 
    exact h.2 x y a b hx hy ha hb hab },
  { intro h,
    apply and.intro h.1,
    intros x y a b hx hy ha hb hab,
    wlog hxy : x<=y using [x y a b, y x b a],
    exact le_total _ _,
    apply or.elim (lt_or_eq_of_le hxy),
    { intros hxy, exact h.2 x y a b hx hy hxy ha hb hab },
    { intros hxy, rw [hxy,←add_smul, hab, one_smul,←add_mul,hab,one_mul] } }
end

lemma convex_on_subset (h_convex_on : convex_on D f) (h_subset : A ⊆ D) (h_convex : convex A) : 
  convex_on A f :=
begin
  apply and.intro h_convex,
  intros x y a b hx hy,
  exact h_convex_on.2 x y a b (h_subset hx) (h_subset hy),
end

lemma convex_on_add (hf : convex_on D f) (hg : convex_on D g): convex_on D (λx, f x + g x) :=
begin
  apply and.intro hf.1,
  intros x y a b hx hy ha hb hab,
  calc
    f (a • x + b • y) + g (a • x + b • y) ≤ (a * f x + b * f y) + (a * g x + b * g y) 
      : add_le_add (hf.2 x y a b hx hy ha hb hab) (hg.2 x y a b hx hy ha hb hab)
    ... = a * f x + a * g x + b * f y + b * g y : by linarith
    ... = a * (f x + g x) + b * (f y + g y) : by simp [mul_add]
end

lemma convex_on_smul (c : ℝ) (hc : 0 ≤ c) (hf : convex_on D f) : convex_on D (λx, c * f x) :=
begin
  apply and.intro hf.1,
  intros x y a b hx hy ha hb hab,
  calc 
    c * f (a • x + b • y) ≤ c * (a * f x + b * f y) 
      : mul_le_mul_of_nonneg_left (hf.2 x y a b hx hy ha hb hab) hc
    ... = a * (c * f x) + b * (c * f y) : by rw mul_add; ac_refl
end

lemma convex_le_of_convex_on (hf : convex_on D f) (r : ℝ): convex { x ∈ D | f x ≤ r } :=
begin
  intros x y a b hx hy ha hb hab,
  simp at *,
  apply and.intro,
  { exact hf.1 x y a b hx.1 hy.1 ha hb hab },
  { apply le_trans (hf.2 x y a b hx.1 hy.1 ha hb hab),
    wlog h_wlog : f x ≤ f y using [x y a b, y x b a],
    apply le_total, 
    calc a * f x + b * f y ≤ a * f y + b * f y : add_le_add (mul_le_mul_of_nonneg_left h_wlog ha) (le_refl _)
                       ... = (a + b) * f y     : (add_mul _ _ _).symm
                       ... ≤ r                 : by rw [hab, one_mul]; exact hy.2
  }
end

lemma convex_lt_of_convex_on (hf : convex_on D f) (r : ℝ): convex { x ∈ D | f x < r } :=
begin
  intros x y a b hx hy ha hb hab,
  simp at *,
  apply and.intro,
  { exact hf.1 x y a b hx.1 hy.1 ha hb hab },
  { apply lt_of_le_of_lt (hf.2 x y a b hx.1 hy.1 ha hb hab),
    wlog h_wlog : f x ≤ f y using [x y a b, y x b a],
    apply le_total, 
    calc a * f x + b * f y ≤ a * f y + b * f y : add_le_add (mul_le_mul_of_nonneg_left h_wlog ha) (le_refl _)
                       ... = (a + b) * f y     : (add_mul _ _ _).symm
                       ... < r                 : by rw [hab, one_mul]; exact hy.2
  }
end

lemma le_on_interval_of_convex_on (x y : α) (a b : ℝ)
  (hf : convex_on D f) (hx : x ∈ D) (hy : y ∈ D) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1):
  f (a • x + b • y) ≤ max (f x) (f y) :=
calc 
  f (a • x + b • y) ≤ a * f x + b * f y : hf.2 x y a b hx hy ha hb hab
  ... ≤ a * max (f x) (f y) + b * max (f x) (f y) : 
    add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha) (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
  ... ≤ max (f x) (f y) : by rw [←add_mul, hab, one_mul]

lemma convex_on_dist {α : Type} [normed_space ℝ α] (z : α) (D : set α) (hD : convex D): 
  convex_on D (λz', dist z' z) := 
begin
  apply and.intro hD,
  intros x y a b hx hy ha hb hab,
  calc
    dist (a • x + b • y) z = ∥ (a • x + b • y) - (a + b) • z ∥
      : by rw [hab, one_smul, normed_group.dist_eq]
    ... = ∥a • (x - z) + b • (y - z)∥
      : by rw [add_smul, smul_sub, smul_sub]; simp
    ... ≤ ∥a • (x - z)∥ + ∥b • (y - z)∥
      : norm_triangle (a • (x - z)) (b • (y - z))
    ... = a * dist x z + b * dist y z :
      by simp [norm_smul, normed_group.dist_eq, real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
end

lemma convex_ball {α : Type} [normed_space ℝ α] (a : α) (r : ℝ) : convex (metric.ball a r) :=
begin
  unfold metric.ball,
  let h := convex_lt_of_convex_on univ (λb, dist b a) (convex_on_dist _  _ convex_univ) r,
  simp at h,
  exact h
end

lemma convex_closed_ball {α : Type} [normed_space ℝ α] (a : α) (r : ℝ) : convex (metric.closed_ball a r) :=
begin
  unfold metric.closed_ball,
  let h := convex_le_of_convex_on univ (λb, dist b a) (convex_on_dist _  _ convex_univ) r,
  simp at h,
  exact h
end

end
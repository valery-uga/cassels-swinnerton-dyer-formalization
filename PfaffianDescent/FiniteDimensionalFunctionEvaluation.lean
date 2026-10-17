import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Finite evaluation witnesses for finite-dimensional function systems

A finite-dimensional space of functions which injects into all functions on a
set is already detected on finitely many points.  This is the linear-algebra
core of the assertion that sufficiently many points impose independent
conditions on a linear system.
-/

namespace PfaffianDescent

universe u v

/-- A square evaluation matrix that is injective over a field remains
injective after any field extension.  This is the linear-algebra step behind
transporting finite interpolation witnesses to coefficient extensions. -/
theorem Matrix.map_mulVec_injective_of_mulVec_injective
    {K L : Type u} {ι : Type v} [Field K] [Field L] [Fintype ι] [DecidableEq ι]
    (f : K →+* L) (A : Matrix ι ι K)
    (hA : Function.Injective A.mulVec) :
    Function.Injective (A.map f).mulVec := by
  have hAunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hA
  have hAmapunit : IsUnit (A.map f) := by
    rw [← RingHom.mapMatrix_apply]
    exact hAunit.map (RingHom.mapMatrix f)
  exact Matrix.mulVec_injective_iff_isUnit.mpr hAmapunit

/-- An injective finite-dimensional system of `K`-valued functions admits a
finite set of evaluation points that detects its zero function. -/
theorem exists_finset_evaluations_detect_zero
    {K X V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] (X → K))
    (hf : Function.Injective f) :
    ∃ s : Finset X, s.card ≤ Module.finrank K V ∧
      ∀ v : V, (∀ x ∈ s, f v x = 0) → v = 0 := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      Module.finrank K V = n → ∀ (f : V →ₗ[K] (X → K)),
        Function.Injective f →
          ∃ s : Finset X, s.card ≤ n ∧
            ∀ v : V, (∀ x ∈ s, f v x = 0) → v = 0
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ hdim g hg
      by_cases hsub : Subsingleton W
      · refine ⟨∅, ?_⟩
        constructor
        · exact Nat.zero_le _
        · intro w _
          exact Subsingleton.elim _ _
      · let _ : Nontrivial W := not_subsingleton_iff_nontrivial.mp hsub
        obtain ⟨w, hw⟩ := exists_ne (0 : W)
        obtain ⟨x, hx⟩ : ∃ x : X, g w x ≠ 0 := by
          by_contra h
          push Not at h
          apply hw
          apply hg
          ext y
          simpa using h y
        let e : W →ₗ[K] K := (LinearMap.proj x).comp g
        have hew : e w ≠ 0 := by
          simpa only [e, LinearMap.comp_apply, LinearMap.proj_apply] using hx
        let U : Submodule K W := LinearMap.ker e
        have hUlt : U < ⊤ := by
          apply lt_top_iff_ne_top.mpr
          intro htop
          have hwU : w ∈ U := by
            rw [htop]
            exact Submodule.mem_top
          exact hew (LinearMap.mem_ker.mp hwU)
        have hUdim : Module.finrank K U < n := by
          have hlt := Submodule.finrank_lt_finrank_of_lt hUlt
          simpa only [finrank_top, hdim] using hlt
        let gU : U →ₗ[K] (X → K) := g.comp U.subtype
        have hgU : Function.Injective gU := by
          intro a b hab
          apply Subtype.ext
          apply hg
          exact hab
        obtain ⟨s, hscard, hs⟩ := ih (Module.finrank K U) hUdim U rfl gU hgU
        refine ⟨insert x s, ?_, ?_⟩
        · calc
            (insert x s).card ≤ s.card + 1 := Finset.card_insert_le _ _
            _ ≤ Module.finrank K U + 1 := Nat.succ_le_succ hscard
            _ ≤ n := Nat.succ_le_of_lt hUdim
        · intro z hz
          have hzx : g z x = 0 := hz x (Finset.mem_insert_self _ _)
          have hez : e z = 0 := by
            simpa only [e, LinearMap.comp_apply, LinearMap.proj_apply] using hzx
          let zU : U := ⟨z, LinearMap.mem_ker.mpr hez⟩
          have hzU : zU = 0 := hs zU (by
            intro y hy
            exact hz y (Finset.mem_insert_of_mem hy))
          exact congrArg Subtype.val hzU
  exact hP (Module.finrank K V) V rfl f hf

/-- Restriction of scalar-valued functions to the points of a finite set. -/
noncomputable def finsetEvaluation {K X : Type u} [Semiring K]
    (s : Finset X) : (X → K) →ₗ[K] (s → K) :=
  { toFun := fun g x => g x.1
    map_add' := by
      intro g h
      rfl
    map_smul' := by
      intro a g
      rfl }

/-- Enlarging a finite set of evaluation points preserves injectivity of the
restriction of a function system. -/
theorem finsetEvaluation_injective_of_subset
    {K X V : Type u} [Semiring K] [AddCommMonoid V] [Module K V]
    (f : V →ₗ[K] (X → K)) {s t : Finset X} (hst : s ⊆ t)
    (hinj : Function.Injective ((finsetEvaluation s).comp f)) :
    Function.Injective ((finsetEvaluation t).comp f) := by
  intro v w hvw
  apply hinj
  ext x
  have hvalue := congrFun hvw ⟨x.1, hst x.2⟩
  change f v x.1 = f w x.1 at hvalue
  exact hvalue

/-- Restricting a surjective evaluation map to a smaller finite set of
points preserves surjectivity.  Values prescribed on the smaller set are
extended by zero to the larger set before applying the original
interpolation theorem. -/
theorem finsetEvaluation_surjective_of_subset
    {K X V : Type u} [Semiring K] [AddCommMonoid V] [Module K V]
    (f : V →ₗ[K] (X → K)) {s t : Finset X} (hts : t ⊆ s)
    (hsurj : Function.Surjective ((finsetEvaluation s).comp f)) :
    Function.Surjective ((finsetEvaluation t).comp f) := by
  classical
  intro z
  let z' : s → K := fun x =>
    if hx : x.1 ∈ t then z ⟨x.1, hx⟩ else 0
  obtain ⟨v, hv⟩ := hsurj z'
  refine ⟨v, ?_⟩
  funext x
  have hxS : x.1 ∈ s := hts x.2
  have hx := congrFun hv ⟨x.1, hxS⟩
  change f v x.1 = z' ⟨x.1, hxS⟩ at hx
  change f v x.1 = z x
  convert hx using 1
  simp only [z', dif_pos x.2]

/-- An injective finite-dimensional system of scalar-valued functions has a
set of exactly `finrank` points on which restriction is still injective. -/
theorem exists_finset_evaluation_injective
    {K X V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] (X → K))
    (hf : Function.Injective f) :
    ∃ s : Finset X, s.card = Module.finrank K V ∧
      Function.Injective ((finsetEvaluation s).comp f) := by
  classical
  obtain ⟨s, hscard, hs⟩ := exists_finset_evaluations_detect_zero f hf
  have hrestriction : Function.Injective ((finsetEvaluation s).comp f) := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hs
    intro x hx
    have hvalue := congrFun hvw ⟨x, hx⟩
    change f v x = f w x at hvalue
    rw [f.map_sub, Pi.sub_apply, sub_eq_zero]
    exact hvalue
  refine ⟨s, ?_, hrestriction⟩
  apply Nat.le_antisymm hscard
  have hdim := LinearMap.finrank_le_finrank_of_injective hrestriction
  rw [Module.finrank_pi_fintype] at hdim
  simpa using hdim

/-- The selected evaluations impose independent conditions: every tuple of
values at the selected points occurs for a unique member of the system. -/
theorem exists_finset_evaluation_bijective
    {K X V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] (X → K))
    (hf : Function.Injective f) :
    ∃ s : Finset X, s.card = Module.finrank K V ∧
      Function.Bijective ((finsetEvaluation s).comp f) := by
  obtain ⟨s, hscard, hinj⟩ := exists_finset_evaluation_injective f hf
  refine ⟨s, hscard, hinj, ?_⟩
  let g := (finsetEvaluation s).comp f
  have hrank : Module.finrank K V = Module.finrank K (s → K) := by
    rw [Module.finrank_pi_fintype]
    simpa using hscard.symm
  exact (LinearEquiv.ofInjectiveOfFinrankEq g hinj hrank).surjective

/-- If a finite set detects a finite-dimensional function system, it contains
a square interpolation subset.  This permits an injective evaluation witness
to be enlarged for geometric purposes while retaining a smaller square matrix
for scalar-extension arguments. -/
theorem exists_finset_subset_evaluation_bijective
    {K X V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] (X → K)) (s : Finset X)
    (hinj : Function.Injective ((finsetEvaluation s).comp f)) :
    ∃ t : Finset X, t ⊆ s ∧ t.card = Module.finrank K V ∧
      Function.Bijective ((finsetEvaluation t).comp f) := by
  classical
  let g : V →ₗ[K] (s → K) := (finsetEvaluation s).comp f
  obtain ⟨r, hrcard, hrbij⟩ := exists_finset_evaluation_bijective g hinj
  let t : Finset X := r.image Subtype.val
  have hts : t ⊆ s := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  have htcard : t.card = Module.finrank K V := by
    change (r.image Subtype.val).card = Module.finrank K V
    rw [Finset.card_image_of_injective r Subtype.val_injective, hrcard]
  have htinj : Function.Injective ((finsetEvaluation t).comp f) := by
    intro v w hvw
    apply hrbij.1
    ext x
    have hmem : (x.1 : X) ∈ t := Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩
    have hvalue := congrFun hvw ⟨(x.1 : X), hmem⟩
    change f v x.1 = f w x.1 at hvalue
    change f v x.1 = f w x.1
    exact hvalue
  refine ⟨t, hts, htcard, htinj, ?_⟩
  let h := (finsetEvaluation t).comp f
  have hrank : Module.finrank K V = Module.finrank K (t → K) := by
    rw [Module.finrank_pi_fintype]
    simpa using htcard.symm
  exact (LinearEquiv.ofInjectiveOfFinrankEq h htinj hrank).surjective

/-- An injective finite-dimensional system of functions on an infinite set
can be tested on any prescribed number of distinct points at least its
dimension.  This supplies witnesses for generic-incidence arguments when a
linear system has no nonzero section vanishing everywhere. -/
theorem exists_embedding_evaluation_injective
    {K X V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite X] (f : V →ₗ[K] (X → K))
    (hf : Function.Injective f) (n : ℕ) (hn : Module.finrank K V ≤ n) :
    ∃ e : Fin n ↪ X,
      Function.Injective
        ({ toFun := fun v i => f v (e i)
           map_add' := by
             intro v w
             ext i
             exact congrFun (f.map_add v w) (e i)
           map_smul' := by
             intro a v
             ext i
             exact congrFun (f.map_smul a v) (e i) } : V →ₗ[K] (Fin n → K)) := by
  classical
  obtain ⟨s, hscard, hsinj⟩ := exists_finset_evaluation_injective f hf
  obtain ⟨t, hst, htcard⟩ := Infinite.exists_superset_card_eq s n (by
    simpa [hscard] using hn)
  let eFin : Fin n ≃ t :=
    (Fintype.equivFinOfCardEq (α := t) (by simpa using htcard)).symm
  let e : Fin n ↪ X := eFin.toEmbedding.trans
    (Function.Embedding.subtype fun x : X => x ∈ t)
  refine ⟨e, ?_⟩
  intro v w hvw
  apply hsinj
  funext x
  obtain ⟨i, hi⟩ := eFin.surjective ⟨x.1, hst x.2⟩
  have hei : e i = x.1 := by
    change (eFin i).1 = x.1
    exact congrArg Subtype.val hi
  have hvalue := congrFun hvw i
  change f v (e i) = f w (e i) at hvalue
  rw [hei] at hvalue
  exact hvalue

/-- If the number of requested points is no larger than the dimension of a
finite-dimensional function system, one can choose distinct points whose
evaluations are independent.  Together with
`exists_embedding_evaluation_injective`, this supplies both alternatives in
the maximal-rank condition for generic marked-point evaluation. -/
theorem exists_embedding_evaluation_surjective
    {K X V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] (X → K))
    (hf : Function.Injective f) (n : ℕ) (hn : n ≤ Module.finrank K V) :
    ∃ e : Fin n ↪ X,
      Function.Surjective
        ({ toFun := fun v i => f v (e i)
           map_add' := by
             intro v w
             ext i
             exact congrFun (f.map_add v w) (e i)
           map_smul' := by
             intro a v
             ext i
             exact congrFun (f.map_smul a v) (e i) } : V →ₗ[K] (Fin n → K)) := by
  classical
  obtain ⟨s, hscard, hsbij⟩ := exists_finset_evaluation_bijective f hf
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq
    (s := s) (n := n) (by rw [hscard]; exact hn)
  have hsurj : Function.Surjective ((finsetEvaluation t).comp f) :=
    finsetEvaluation_surjective_of_subset f hts hsbij.2
  let eFin : Fin n ≃ t :=
    (Fintype.equivFinOfCardEq (α := t) (by simpa using htcard)).symm
  let e : Fin n ↪ X := eFin.toEmbedding.trans
    (Function.Embedding.subtype fun x : X => x ∈ t)
  refine ⟨e, ?_⟩
  intro z
  let zt : t → K := fun x => z (eFin.symm x)
  obtain ⟨v, hv⟩ := hsurj zt
  refine ⟨v, ?_⟩
  funext i
  have hvalue := congrFun hv (eFin i)
  change f v (e i) = zt (eFin i) at hvalue
  change f v (e i) = z i
  simpa only [zt, eFin.symm_apply_apply] using hvalue

/-- A faithful finite-dimensional function system has an evaluation map of
maximal rank at some configuration of any prescribed size.  This witness is
the nonemptiness input for the open maximal-rank locus of marked points. -/
theorem exists_embedding_evaluation_maximal_rank
    {K X V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite X]
    (f : V →ₗ[K] (X → K)) (hf : Function.Injective f) (n : ℕ) :
    ∃ e : Fin n ↪ X,
      Function.Surjective
        ({ toFun := fun v i => f v (e i)
           map_add' := by
             intro v w
             ext i
             exact congrFun (f.map_add v w) (e i)
           map_smul' := by
             intro a v
             ext i
             exact congrFun (f.map_smul a v) (e i) } : V →ₗ[K] (Fin n → K)) ∨
      Function.Injective
        ({ toFun := fun v i => f v (e i)
           map_add' := by
             intro v w
             ext i
             exact congrFun (f.map_add v w) (e i)
           map_smul' := by
             intro a v
             ext i
             exact congrFun (f.map_smul a v) (e i) } : V →ₗ[K] (Fin n → K)) := by
  by_cases hdim : Module.finrank K V ≤ n
  · obtain ⟨e, he⟩ := exists_embedding_evaluation_injective f hf n hdim
    exact ⟨e, Or.inr he⟩
  · have hn : n ≤ Module.finrank K V := by omega
    obtain ⟨e, he⟩ := exists_embedding_evaluation_surjective f hf n hn
    exact ⟨e, Or.inl he⟩

/-- A surjective evaluation map has chosen interpolation sections whose
evaluation matrix is the identity. The same matrix remains the identity
after any field extension, so evaluation stays surjective over the residue
fields used by an incidence family. -/
theorem surjective_evaluation_has_extension_stable_interpolation_frame
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) (evaluation : V →ₗ[K] (Fin n → K))
    (hsurj : Function.Surjective evaluation) :
    ∃ q : Fin n → V,
      ∀ {L : Type u} [Field L] (g : K →+* L) (z : Fin n → L) (i : Fin n),
        (∑ j : Fin n, g (evaluation (q j) i) * z j) = z i := by
  classical
  let q : Fin n → V := fun j =>
    Classical.choose (hsurj (Pi.single j 1))
  have hq (j : Fin n) : evaluation (q j) = Pi.single j 1 :=
    Classical.choose_spec (hsurj (Pi.single j 1))
  refine ⟨q, ?_⟩
  intro L _ g z i
  have hqij (j : Fin n) : evaluation (q j) i = if i = j then 1 else 0 := by
    rw [hq]
    simp [Pi.single_apply]
  simp_rw [hqij]
  simp

/-- One square set of evaluation points detects coefficient vectors after
every extension of the coefficient field.  The matrix is formed from the
chosen finite basis of the original function system; its invertibility is
preserved by `Matrix.map`. -/
theorem exists_embedding_basisEvaluation_injective_after_fieldExtension
    {K X V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite X]
    (f : V →ₗ[K] (X → K)) (hf : Function.Injective f) :
    ∃ e : Fin (Module.finrank K V) ↪ X,
      ∀ {L : Type u} [Field L] (g : K →+* L),
        Function.Injective
          (fun c : Fin (Module.finrank K V) → L => fun i =>
            ∑ j, g (f (Module.finBasis K V j) (e i)) * c j) := by
  classical
  let b := Module.finBasis K V
  obtain ⟨e, he⟩ := exists_embedding_evaluation_injective
    f hf (Module.finrank K V) le_rfl
  refine ⟨e, ?_⟩
  let A : Matrix (Fin (Module.finrank K V))
      (Fin (Module.finrank K V)) K :=
    fun i j => f (b j) (e i)
  have hformula (c : Fin (Module.finrank K V) → K)
      (i : Fin (Module.finrank K V)) :
      A.mulVec c i = f (b.equivFun.symm c) (e i) := by
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    simp only [A, Matrix.mulVec, Finset.sum_apply]
    change (∑ j, f (b j) (e i) * c j) =
      ∑ j, f (c j • b j) (e i)
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hA : Function.Injective A.mulVec := by
    intro c d hcd
    apply b.equivFun.symm.injective
    apply he
    funext i
    change f (b.equivFun.symm c) (e i) =
      f (b.equivFun.symm d) (e i)
    rw [← hformula c i, ← hformula d i]
    exact congrFun hcd i
  intro L _ g
  have hmap := Matrix.map_mulVec_injective_of_mulVec_injective g A hA
  change Function.Injective (A.map g).mulVec
  exact hmap

/-- The extension-stable square evaluation witness can be enlarged to any
prescribed number of distinct points at least the dimension.  Consequently
the same `n`-point configuration detects every scalar-extended member of the
linear system. -/
theorem exists_embedding_basisEvaluation_injective_after_fieldExtension_of_finrank_le
    {K X V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite X]
    (f : V →ₗ[K] (X → K)) (hf : Function.Injective f)
    (n : ℕ) (hn : Module.finrank K V ≤ n) :
    ∃ e : Fin n ↪ X,
      ∀ {L : Type u} [Field L] (g : K →+* L),
        Function.Injective
          (fun c : Fin (Module.finrank K V) → L => fun i =>
            ∑ j, g (f (Module.finBasis K V j) (e i)) * c j) := by
  classical
  obtain ⟨e₀, he₀⟩ :=
    exists_embedding_basisEvaluation_injective_after_fieldExtension f hf
  let s : Finset X := Finset.univ.map e₀
  have hscard : s.card = Module.finrank K V := by
    simp [s]
  obtain ⟨t, hst, htcard⟩ := Infinite.exists_superset_card_eq s n (by
    simpa [hscard] using hn)
  let eFin : Fin n ≃ t :=
    (Fintype.equivFinOfCardEq (α := t) (by simpa using htcard)).symm
  let e : Fin n ↪ X := eFin.toEmbedding.trans
    (Function.Embedding.subtype fun x : X => x ∈ t)
  refine ⟨e, ?_⟩
  intro L _ g c d hcd
  apply he₀ g
  funext i
  have hiS : e₀ i ∈ s :=
    Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨k, hk⟩ := eFin.surjective ⟨e₀ i, hst hiS⟩
  have hek : e k = e₀ i := by
    change (eFin k).1 = e₀ i
    exact congrArg Subtype.val hk
  have hvalue := congrFun hcd k
  change (∑ j, g (f (Module.finBasis K V j) (e k)) * c j) =
    ∑ j, g (f (Module.finBasis K V j) (e k)) * d j at hvalue
  rw [hek] at hvalue
  exact hvalue

/-- The finite detection result for a system whose value at each point has
several scalar coordinates.  The selected base points may be tested in every
coordinate, so this applies to local frames of a vector bundle. -/
theorem exists_finset_vectorFiber_evaluations_detect_zero
    {K X I V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] (X → I → K))
    (hf : Function.Injective f) :
    ∃ s : Finset X, s.card ≤ Module.finrank K V ∧
      ∀ v : V, (∀ x ∈ s, ∀ i : I, f v x i = 0) → v = 0 := by
  classical
  let f' : V →ₗ[K] ((X × I) → K) :=
  {
    toFun v := fun xi => f v xi.1 xi.2
    map_add' v w := by
      ext xi
      exact congrFun (congrFun (f.map_add v w) xi.1) xi.2
    map_smul' a v := by
      ext xi
      exact congrFun (congrFun (f.map_smul a v) xi.1) xi.2
  }
  have hf' : Function.Injective f' := by
    intro v w hvw
    apply hf
    ext x i
    change f' v ⟨x, i⟩ = f' w ⟨x, i⟩
    exact congrFun hvw ⟨x, i⟩
  obtain ⟨t, htcard, ht⟩ := exists_finset_evaluations_detect_zero f' hf'
  refine ⟨t.image Prod.fst, Finset.card_image_le.trans htcard, ?_⟩
  intro v hv
  apply ht v
  intro xi hxi
  exact hv xi.1 (Finset.mem_image.mpr ⟨xi, hxi, rfl⟩) xi.2

/-- A finite-dimensional system of sections with values in arbitrary local
coordinate fibres can be tested at any prescribed number of distinct base
points at least its dimension.  All fibre coordinates are retained at each
selected point.  This is the finite-frame form of the independent-point
witness used for rank-two section zero loci. -/
theorem exists_embedding_vectorFiber_evaluation_injective
    {K X I V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite X] (f : V →ₗ[K] (X → I → K))
    (hf : Function.Injective f) (n : ℕ) (hn : Module.finrank K V ≤ n) :
    ∃ e : Fin n ↪ X,
      Function.Injective
        ({ toFun := fun v i j => f v (e i) j
           map_add' := by
             intro v w
             ext i j
             exact congrFun (congrFun (f.map_add v w) (e i)) j
           map_smul' := by
             intro a v
             ext i j
             exact congrFun (congrFun (f.map_smul a v) (e i)) j } :
          V →ₗ[K] (Fin n → I → K)) := by
  classical
  obtain ⟨s, hscard, hs⟩ := exists_finset_vectorFiber_evaluations_detect_zero f hf
  have hsinj : Function.Injective
      ({ toFun := fun v x i => f v x.1 i
         map_add' := by
           intro v w
           ext x i
           exact congrFun (congrFun (f.map_add v w) x.1) i
         map_smul' := by
           intro a v
           ext x i
           exact congrFun (congrFun (f.map_smul a v) x.1) i } :
        V →ₗ[K] (s → I → K)) := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hs
    intro x hx i
    have hvalue := congrFun (congrFun hvw ⟨x, hx⟩) i
    change f v x i = f w x i at hvalue
    rw [f.map_sub, Pi.sub_apply, Pi.sub_apply, sub_eq_zero]
    exact hvalue
  obtain ⟨t, hst, htcard⟩ := Infinite.exists_superset_card_eq s n
    (hscard.trans hn)
  let eFin : Fin n ≃ t :=
    (Fintype.equivFinOfCardEq (α := t) (by simpa using htcard)).symm
  let e : Fin n ↪ X := eFin.toEmbedding.trans
    (Function.Embedding.subtype fun x : X => x ∈ t)
  refine ⟨e, ?_⟩
  intro v w hvw
  apply hsinj
  ext x i
  obtain ⟨j, hj⟩ := eFin.surjective ⟨x.1, hst x.2⟩
  have hej : e j = x.1 := by
    change (eFin j).1 = x.1
    exact congrArg Subtype.val hj
  have hvalue := congrFun (congrFun hvw j) i
  change f v (e j) i = f w (e j) i at hvalue
  rw [hej] at hvalue
  exact hvalue

end PfaffianDescent

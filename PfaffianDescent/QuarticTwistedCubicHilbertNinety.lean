import PfaffianDescent.QuarticTwistedCubicBrauerObstruction
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The averaging step in matrix Hilbert 90

For a finite group acting on a field and a matrix-valued descent cocycle, the
usual Hilbert--90 averaging operator produces matrices satisfying the desired
semilinear covariance.  The results here isolate that calculation.  The
remaining existence statement, that one such average is invertible for a
finite Galois action, is the final algebraic input needed for Hilbert 90.
-/

namespace PfaffianDescent.QuarticNet.ProjectiveCocycle

open Matrix
open scoped BigOperators MatrixGroups

universe u v

variable {L : Type u} [Field L] {G : Type v} [Group G]

/-- A normalized linear descent cocycle takes the identity group element to
the identity matrix. -/
lemma LinearCocycle.map_one {n : ℕ} {rho : G →* L ≃+* L}
    (a : LinearCocycle (L := L) (G := G) n rho) : a.toFun 1 = 1 := by
  have hrho : rho 1 = 1 := rho.map_one
  have hmap (X : GL (Fin n) L) :
      Matrix.GeneralLinearGroup.map (rho 1).toRingHom X = X := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [hrho]
  have h := a.map_mul' 1 1
  rw [hmap] at h
  simp only [one_mul] at h
  apply mul_left_cancel (a := a.toFun 1)
  simpa using h.symm

/-- The standard averaging operator for a linear descent cocycle. -/
noncomputable def LinearCocycle.average [Fintype G] {n : ℕ} {rho : G →* L ≃+* L}
    (a : LinearCocycle (L := L) (G := G) n rho)
    (B : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  ∑ h : G, B.map (rho h).toRingHom * (↑((a.toFun h)⁻¹) : Matrix (Fin n) (Fin n) L)

/-- Rewrite one cocycle coefficient after applying the field automorphism
indexed by the left factor. -/
lemma LinearCocycle.map_value_eq {n : ℕ} {rho : G →* L ≃+* L}
    (a : LinearCocycle (L := L) (G := G) n rho) (g h : G) :
    Matrix.GeneralLinearGroup.map (rho g).toRingHom (a.toFun h) =
      (a.toFun g)⁻¹ * a.toFun (g * h) := by
  calc
    Matrix.GeneralLinearGroup.map (rho g).toRingHom (a.toFun h) =
        1 * Matrix.GeneralLinearGroup.map (rho g).toRingHom (a.toFun h) := by rw [one_mul]
    _ = ((a.toFun g)⁻¹ * a.toFun g) *
        Matrix.GeneralLinearGroup.map (rho g).toRingHom (a.toFun h) := by
      rw [inv_mul_cancel]
    _ = (a.toFun g)⁻¹ *
        (a.toFun g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (a.toFun h)) := by
      rw [mul_assoc]
    _ = (a.toFun g)⁻¹ * a.toFun (g * h) := by rw [← a.map_mul']

/-- The inverse matrix in one summand of the averaging operator transforms
into the inverse corresponding to the translated group element. -/
lemma LinearCocycle.map_inv_value_eq {n : ℕ} {rho : G →* L ≃+* L}
    (a : LinearCocycle (L := L) (G := G) n rho) (g h : G) :
    Matrix.GeneralLinearGroup.map (rho g).toRingHom ((a.toFun h)⁻¹) =
      (a.toFun (g * h))⁻¹ * a.toFun g := by
  rw [Matrix.GeneralLinearGroup.map_inv, a.map_value_eq]
  simp only [_root_.mul_inv_rev, inv_inv]

/-- The covariance formula for one summand in the Hilbert--90 average. -/
lemma LinearCocycle.map_average_term {n : ℕ} {rho : G →* L ≃+* L}
    (a : LinearCocycle (L := L) (G := G) n rho)
    (B : Matrix (Fin n) (Fin n) L) (g h : G) :
    (B.map (rho h).toRingHom * (↑((a.toFun h)⁻¹) : Matrix (Fin n) (Fin n) L)).map
        (rho g).toRingHom =
      (B.map (rho (g * h)).toRingHom *
        (↑((a.toFun (g * h))⁻¹) : Matrix (Fin n) (Fin n) L)) *
          (a.toFun g : Matrix (Fin n) (Fin n) L) := by
  rw [Matrix.map_mul]
  have hrho : (rho g).toRingHom ∘ (rho h).toRingHom = (rho (g * h)).toRingHom := by
    ext x
    rw [rho.map_mul]
    rfl
  rw [Matrix.map_map, hrho]
  change B.map (rho (g * h)).toRingHom *
      (↑((a.toFun h)⁻¹) : Matrix (Fin n) (Fin n) L).map (rho g).toRingHom = _
  change B.map (rho (g * h)).toRingHom *
      (Matrix.GeneralLinearGroup.map (rho g).toRingHom ((a.toFun h)⁻¹) :
        Matrix (Fin n) (Fin n) L) = _
  rw [a.map_inv_value_eq]
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]
  rw [mul_assoc]

/-- Averaging produces a matrix with the covariance required to trivialize
an honest linear descent cocycle. -/
lemma LinearCocycle.average_covariant [Fintype G] {n : ℕ} {rho : G →* L ≃+* L}
    (a : LinearCocycle (L := L) (G := G) n rho)
    (B : Matrix (Fin n) (Fin n) L) (g : G) :
    (a.average B).map (rho g).toRingHom =
      a.average B * (a.toFun g : Matrix (Fin n) (Fin n) L) := by
  have map_sum_matrix (f : G → Matrix (Fin n) (Fin n) L) :
      (∑ h : G, f h).map (rho g).toRingHom =
        ∑ h : G, (f h).map (rho g).toRingHom := by
    change (∑ h : G, f h).map (rho g) = ∑ h : G, (f h).map (rho g)
    simpa only [RingEquiv.mapMatrix_apply] using
      (map_sum (RingEquiv.mapMatrix (rho g)) f Finset.univ)
  simp only [LinearCocycle.average]
  rw [map_sum_matrix]
  simp_rw [a.map_average_term B g]
  let f : G → Matrix (Fin n) (Fin n) L := fun h =>
    B.map (rho h).toRingHom * (↑((a.toFun h)⁻¹) : Matrix (Fin n) (Fin n) L)
  change (∑ h : G, f (g * h) * (a.toFun g : Matrix (Fin n) (Fin n) L)) =
    (∑ h : G, f h) * (a.toFun g : Matrix (Fin n) (Fin n) L)
  rw [← Finset.sum_mul]
  exact congrArg (fun X => X * (a.toFun g : Matrix (Fin n) (Fin n) L))
    (Equiv.sum_comp (Equiv.mulLeft g) f)

def rowFunctional {n : ℕ} (r : Fin n → L) : Module.Dual L (Fin n → L) where
  toFun v := r ⬝ᵥ v
  map_add' x y := by
    simp only [dotProduct, Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' c v := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ x, r x * (c * v x)) = ∑ x, c * (r x * v x) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = c * ∑ x, r x * v x := (Finset.mul_sum _ _ _).symm

@[simp] lemma rowFunctional_apply {n : ℕ} (r v : Fin n → L) : rowFunctional r v = r ⬝ᵥ v := rfl


noncomputable def LinearCocycle.rowAverage [Fintype G] {n : ℕ} {rho : G →* L ≃+* L}
    (a : LinearCocycle (L := L) (G := G) n rho) (b : Fin n → L) : Fin n → L :=
  fun j => ∑ h : G, ∑ k : Fin n,
    rho h (b k) * (↑((a.toFun h)⁻¹) : Matrix (Fin n) (Fin n) L) k j

lemma LinearCocycle.average_apply_eq_rowAverage [Fintype G] {n : ℕ} {rho : G →* L ≃+* L}
    (a : LinearCocycle (L := L) (G := G) n rho)
    (B : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    a.average B i j = a.rowAverage (B i) j := by
  classical
  have sum_apply_matrix (f : G → Matrix (Fin n) (Fin n) L) (i j : Fin n) :
      (∑ h : G, f h) i j = ∑ h : G, f h i j := by
    have finset_sum_apply_matrix (s : Finset G) :
        (∑ h ∈ s, f h) i j = ∑ h ∈ s, f h i j := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact congrArg₂ (· + ·) rfl ih
    exact finset_sum_apply_matrix Finset.univ
  simp only [LinearCocycle.average, LinearCocycle.rowAverage]
  rw [sum_apply_matrix]
  simp [Matrix.mul_apply]



/-- The coefficient form of Artin independence for a finite group of field
automorphisms. -/
def IsArtinIndependent [Fintype G] (rho : G →* L ≃+* L) : Prop :=
  ∀ c : G → L, (∀ x : L, ∑ g : G, c g * rho g x = 0) → ∀ g, c g = 0

lemma LinearCocycle.average_right_annihilator_eq_zero [Fintype G] {n : ℕ} [Nonempty (Fin n)]
    {rho : G →* L ≃+* L} (a : LinearCocycle (L := L) (G := G) n rho)
    (hArtin : IsArtinIndependent rho) (v : Fin n → L)
    (hv : ∀ B : Matrix (Fin n) (Fin n) L, a.average B *ᵥ v = 0) : v = 0 := by
  classical
  let i : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
  have hcoeff (j : Fin n) (g : G) :
      ((↑((a.toFun g)⁻¹) : Matrix (Fin n) (Fin n) L) *ᵥ v) j = 0 := by
    let c : G → L := fun h =>
      ((↑((a.toFun h)⁻¹) : Matrix (Fin n) (Fin n) L) *ᵥ v) j
    have hc : ∀ x : L, ∑ h : G, c h * rho h x = 0 := by
      intro x
      have hzero := congrFun (hv (Matrix.single i j x)) i
      rw [LinearCocycle.average, Matrix.sum_mulVec] at hzero
      have hzero' : ∑ h : G,
          (((Matrix.single i j x).map (rho h).toRingHom *
            (↑((a.toFun h)⁻¹) : Matrix (Fin n) (Fin n) L)) *ᵥ v) i = 0 := by
        simpa only [Fintype.sum_apply, Pi.zero_apply] using hzero
      have hsingle (h : G) :
          (Matrix.single i j x).map (rho h).toRingHom =
            Matrix.single i j (rho h x) := by
        ext r s
        by_cases hrs : i = r ∧ j = s
        · simp [hrs]
        · simp [hrs]
      simp_rw [← Matrix.mulVec_mulVec, hsingle] at hzero'
      simpa only [Matrix.single_mulVec, Function.update_self, c, mul_comm] using hzero' 
    exact hArtin c hc g
  have hinv : (↑((a.toFun 1)⁻¹) : Matrix (Fin n) (Fin n) L) *ᵥ v = 0 := by
    ext j
    exact hcoeff j 1
  apply Matrix.mulVec_injective_of_isUnit (Units.isUnit ((a.toFun 1)⁻¹))
  simpa using hinv


lemma LinearCocycle.rowAverage_right_annihilator_eq_zero [Fintype G] {n : ℕ} [Nonempty (Fin n)]
    {rho : G →* L ≃+* L} (a : LinearCocycle (L := L) (G := G) n rho)
    (hArtin : IsArtinIndependent rho) (v : Fin n → L)
    (hv : ∀ b : Fin n → L, a.rowAverage b ⬝ᵥ v = 0) : v = 0 := by
  apply a.average_right_annihilator_eq_zero hArtin v
  intro B
  ext i
  rw [Matrix.mulVec_apply]
  have hrow : (a.average B).row i = a.rowAverage (B i) := by
    ext j
    exact a.average_apply_eq_rowAverage B i j
  rw [hrow]
  exact hv (B i)


lemma LinearCocycle.span_rowFunctionals_eq_top [Fintype G] {n : ℕ} [Nonempty (Fin n)]
    {rho : G →* L ≃+* L} (a : LinearCocycle (L := L) (G := G) n rho)
    (hArtin : IsArtinIndependent rho) :
    Submodule.span L (Set.range fun b : Fin n → L => rowFunctional (a.rowAverage b)) = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro z hzne
  by_contra h
  push Not at h
  apply hzne
  apply a.rowAverage_right_annihilator_eq_zero hArtin z
  intro b
  have hb := h (rowFunctional (a.rowAverage b)) ⟨b, rfl⟩
  simpa only [rowFunctional_apply] using hb


theorem LinearCocycle.exists_invertible_average_of_artin_of_ne_zero [Fintype G]
    {n : ℕ} {rho : G →* L ≃+* L} (a : LinearCocycle (L := L) (G := G) n rho)
    (hArtin : IsArtinIndependent rho) (hn : n ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin n) L, (a.average B).det ≠ 0 := by
  classical
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  letI : Nonempty (Fin n) := ⟨i⟩
  let s : Set (Module.Dual L (Fin n → L)) :=
    Set.range fun b : Fin n → L => rowFunctional (a.rowAverage b)
  have hs : Submodule.span L s = ⊤ := by
    simpa only [s] using a.span_rowFunctionals_eq_top hArtin
  have hfin : Module.finrank L ↥(Submodule.span L s) = n := by
    rw [hs, finrank_top, Subspace.dual_finrank_eq, Module.finrank_fin_fun]
  obtain ⟨f, hfm, hfs, hfli⟩ := Submodule.exists_fun_fin_finrank_span_eq L s
  let e : Fin n ≃ Fin (Module.finrank L ↥(Submodule.span L s)) := {
    toFun := Fin.cast hfin.symm
    invFun := Fin.cast hfin
    left_inv := by intro i; apply Fin.ext; rfl
    right_inv := by intro i; apply Fin.ext; rfl }
  let f₂ : Fin n → Module.Dual L (Fin n → L) := f ∘ e
  have hfm₂ (i : Fin n) : f₂ i ∈ s := hfm (e i)
  have hrange : Set.range f₂ = Set.range f := by
    ext φ
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective i
      refine ⟨j, ?_⟩
      simp only [f₂, Function.comp_apply, hj]
  simp only [s, Set.mem_range] at hfm₂
  choose b hb using hfm₂
  let B : Matrix (Fin n) (Fin n) L := fun i j => b i j
  have hrowvec (i : Fin n) : (a.average B).row i = a.rowAverage (b i) := by
    ext j
    change a.average B i j = a.rowAverage (b i) j
    simpa only [B] using a.average_apply_eq_rowAverage B i j
  have hrow (i : Fin n) : rowFunctional ((a.average B).row i) = f₂ i := by
    rw [hrowvec]
    exact hb i
  have hspan : Submodule.span L (Set.range f₂) = ⊤ := by
    rw [hrange, hfs, hs]
  have hinj : Function.Injective (a.average B).mulVec := by
    intro x y hxy
    have hzero : a.average B *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hfi (i : Fin n) : f₂ i (x - y) = 0 := by
      rw [← hrow]
      exact congrFun hzero i
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff L (x - y)).mp
    intro φ
    obtain ⟨c, hc⟩ :=
      Submodule.mem_span_range_iff_exists_fun L |>.mp (show φ ∈ Submodule.span L (Set.range f₂) by
        rw [hspan]
        exact Submodule.mem_top)
    rw [← hc]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hfi, mul_zero,
      Finset.sum_const_zero]
  refine ⟨B, ?_⟩
  have hunit : IsUnit (a.average B) := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit))

/-- The binary instance of the preceding dimension-independent averaging
argument. -/
theorem LinearCocycle.exists_invertible_average_of_artin [Fintype G]
    {rho : G →* L ≃+* L} (a : LinearCocycle (L := L) (G := G) 2 rho)
    (hArtin : IsArtinIndependent rho) :
    ∃ B : Matrix (Fin 2) (Fin 2) L, (a.average B).det ≠ 0 :=
  a.exists_invertible_average_of_artin_of_ne_zero hArtin (by omega)


/-- If one Hilbert--90 average is invertible, the cocycle is a coboundary.
The remaining field-theoretic part of Hilbert 90 is precisely the existence
of such an invertible average for a finite Galois action. -/
theorem LinearCocycle.isCoboundary_of_average_eq [Fintype G] {n : ℕ}
    {rho : G →* L ≃+* L}
    (a : LinearCocycle (L := L) (G := G) n rho)
    (B : Matrix (Fin n) (Fin n) L) (X : GL (Fin n) L)
    (hX : (X : Matrix (Fin n) (Fin n) L) = a.average B) : a.IsCoboundary := by
  refine ⟨X, ?_⟩
  intro g
  have hcovMat : (X : Matrix (Fin n) (Fin n) L).map (rho g).toRingHom =
      (X : Matrix (Fin n) (Fin n) L) * (a.toFun g : Matrix (Fin n) (Fin n) L) := by
    rw [hX]
    exact a.average_covariant B g
  have hcov : Matrix.GeneralLinearGroup.map (rho g).toRingHom X = X * a.toFun g := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_mul]
    simpa only [Matrix.map_apply] using congrFun (congrFun hcovMat i) j
  calc
    a.toFun g = 1 * a.toFun g := by rw [one_mul]
    _ = (X⁻¹ * X) * a.toFun g := by rw [inv_mul_cancel]
    _ = X⁻¹ * (X * a.toFun g) := by rw [mul_assoc]
    _ = X⁻¹ * Matrix.GeneralLinearGroup.map (rho g).toRingHom X := by rw [hcov]

theorem LinearCocycle.isCoboundary_of_artin_of_ne_zero [Fintype G]
    {n : ℕ} {rho : G →* L ≃+* L} (a : LinearCocycle (L := L) (G := G) n rho)
    (hArtin : IsArtinIndependent rho) (hn : n ≠ 0) : a.IsCoboundary := by
  obtain ⟨B, hB⟩ := a.exists_invertible_average_of_artin_of_ne_zero hArtin hn
  let X : GL (Fin n) L := Matrix.GeneralLinearGroup.mkOfDetNeZero (a.average B) hB
  apply a.isCoboundary_of_average_eq B X
  rfl

/-- The binary Hilbert--90 statement used by the twisted-cubic cocycle. -/
theorem LinearCocycle.isCoboundary_of_artin [Fintype G]
    {rho : G →* L ≃+* L} (a : LinearCocycle (L := L) (G := G) 2 rho)
    (hArtin : IsArtinIndependent rho) : a.IsCoboundary :=
  a.isCoboundary_of_artin_of_ne_zero hArtin (by omega)


end PfaffianDescent.QuarticNet.ProjectiveCocycle

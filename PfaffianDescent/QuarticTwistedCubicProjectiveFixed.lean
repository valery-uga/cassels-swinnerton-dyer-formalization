import PfaffianDescent.QuarticTwistedCubicHilbertNinetyGalois

/-!
# Descent of Galois-fixed projective coordinates

The geometric twisted-cubic argument will produce a projective coordinate
change over a finite Galois splitting field.  This file proves the linear
descent fact needed at the end of that argument: a fixed projective change is
defined over the ground field.
-/

namespace PfaffianDescent.QuarticNet.ProjectiveCocycle

open Matrix
open scoped MatrixGroups

universe u v

lemma scalarGL_injective {L : Type u} [Field L] {n : ℕ} (hn : n ≠ 0) :
    Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin n) : Lˣ → GL (Fin n) L) := by
  intro a b hab
  apply Units.ext
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hmatrix :
      (((Matrix.GeneralLinearGroup.scalar (Fin n) a : GL (Fin n) L) :
          Matrix (Fin n) (Fin n) L)) =
        (((Matrix.GeneralLinearGroup.scalar (Fin n) b : GL (Fin n) L) :
          Matrix (Fin n) (Fin n) L)) :=
    congrArg (fun z : GL (Fin n) L => (z : Matrix (Fin n) (Fin n) L)) hab
  have hii := congrFun (congrFun hmatrix i) i
  simpa [i, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply] using hii

lemma glOne_eq_scalar_det {L : Type u} [Field L] (X : GL (Fin 1) L) :
    X = Matrix.GeneralLinearGroup.scalar (Fin 1) X.det := by
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

/-- An entrywise Galois-fixed matrix over a finite Galois field is the scalar
extension of a ground-field matrix. -/
theorem exists_matrix_of_galois_fixed
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) L)
    (hZ : ∀ σ : Gal(L/K), ∀ i j, σ (Z i j) = Z i j) :
    ∃ C : Matrix (Fin n) (Fin n) K, C.map (algebraMap K L) = Z := by
  choose c hc using fun i j =>
    (IsGalois.mem_range_algebraMap_iff_fixed (Z i j)).mpr (fun σ => hZ σ i j)
  refine ⟨c, ?_⟩
  ext i j
  exact hc i j

/-- If the descended matrix becomes invertible over the extension, it was
already invertible over the ground field. -/
theorem matrix_det_ne_zero_of_map_eq
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] {n : ℕ}
    (C : Matrix (Fin n) (Fin n) K) (Z : Matrix (Fin n) (Fin n) L)
    (hC : C.map (algebraMap K L) = Z) (hZ : Z.det ≠ 0) : C.det ≠ 0 := by
  intro hzero
  apply hZ
  calc
    Z.det = (C.map (algebraMap K L)).det := congrArg Matrix.det hC.symm
    _ = algebraMap K L C.det := (RingHom.map_det (algebraMap K L) C).symm
    _ = 0 := by rw [hzero, map_zero]

/-- The scalar by which a chosen matrix representative must be corrected
after applying a Galois automorphism, when its projective class is fixed. -/
noncomputable def pglFixedCorrection
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] {n : ℕ}
    (X : GL (Fin n) L)
    (hX : ∀ σ : Gal(L/K),
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map (galFieldAction K L σ).toRingHom X) =
        Matrix.ProjGenLinGroup.mk X)
    (σ : Gal(L/K)) : Lˣ :=
  (Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp (hX σ)).choose

lemma pglFixedCorrection_spec
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] {n : ℕ}
    (X : GL (Fin n) L)
    (hX : ∀ σ : Gal(L/K),
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map (galFieldAction K L σ).toRingHom X) =
        Matrix.ProjGenLinGroup.mk X)
    (σ : Gal(L/K)) :
    Matrix.GeneralLinearGroup.map (galFieldAction K L σ).toRingHom X *
      Matrix.GeneralLinearGroup.scalar (Fin n) (pglFixedCorrection K L X hX σ) = X :=
  (Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp (hX σ)).choose_spec

lemma pglFixedCorrection_mul
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] {n : ℕ}
    (hn : n ≠ 0) (X : GL (Fin n) L)
    (hX : ∀ σ : Gal(L/K),
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map (galFieldAction K L σ).toRingHom X) =
        Matrix.ProjGenLinGroup.mk X)
    (σ τ : Gal(L/K)) :
    pglFixedCorrection K L X hX (σ * τ) =
      Units.map (galFieldAction K L σ).toRingHom.toMonoidHom
        (pglFixedCorrection K L X hX τ) * pglFixedCorrection K L X hX σ := by
  let u : Gal(L/K) → Lˣ := pglFixedCorrection K L X hX
  let F : Gal(L/K) → GL (Fin n) L := fun g =>
    Matrix.GeneralLinearGroup.map (galFieldAction K L g).toRingHom X
  have hFmap (g h : Gal(L/K)) :
      Matrix.GeneralLinearGroup.map (galFieldAction K L g).toRingHom (F h) = F (g * h) := by
    apply Units.ext
    change ((X : Matrix (Fin n) (Fin n) L).map
      (galFieldAction K L h).toRingHom).map (galFieldAction K L g).toRingHom =
        (X : Matrix (Fin n) (Fin n) L).map (galFieldAction K L (g * h)).toRingHom
    rw [Matrix.map_map]
    rw [(galFieldAction K L).map_mul]
    rfl
  have hspec (g : Gal(L/K)) : F g * Matrix.GeneralLinearGroup.scalar (Fin n) (u g) = X := by
    exact pglFixedCorrection_spec K L X hX g
  have htrans : F (σ * τ) * Matrix.GeneralLinearGroup.scalar (Fin n)
      (Units.map (galFieldAction K L σ).toRingHom.toMonoidHom (u τ)) = F σ := by
    have h := congrArg (Matrix.GeneralLinearGroup.map (galFieldAction K L σ).toRingHom)
      (hspec τ)
    rw [Matrix.GeneralLinearGroup.map_mul,
      Matrix.GeneralLinearGroup.map_scalar, hFmap] at h
    exact h
  have hcomb : F (σ * τ) * Matrix.GeneralLinearGroup.scalar (Fin n)
      (Units.map (galFieldAction K L σ).toRingHom.toMonoidHom (u τ) * u σ) = X := by
    rw [(Matrix.GeneralLinearGroup.scalar (Fin n)).map_mul, ← mul_assoc, htrans]
    exact hspec σ
  apply scalarGL_injective hn
  apply mul_left_cancel (a := F (σ * τ))
  rw [hspec (σ * τ), hcomb]

/-- The inverses of the correction scalars form the honest one-dimensional
linear cocycle whose Hilbert--90 trivialization rescales a projective matrix
representative to a fixed matrix. -/
noncomputable def pglFixedScalarCocycle
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] {n : ℕ}
    (hn : n ≠ 0) (X : GL (Fin n) L)
    (hX : ∀ σ : Gal(L/K),
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map (galFieldAction K L σ).toRingHom X) =
        Matrix.ProjGenLinGroup.mk X) :
    LinearCocycle (L := L) (G := Gal(L/K)) 1 (galFieldAction K L) where
  toFun σ := Matrix.GeneralLinearGroup.scalar (Fin 1)
    (pglFixedCorrection K L X hX σ)⁻¹
  map_mul' σ τ := by
    let u : Gal(L/K) → Lˣ := pglFixedCorrection K L X hX
    rw [Matrix.GeneralLinearGroup.map_scalar,
      ← (Matrix.GeneralLinearGroup.scalar (Fin 1)).map_mul]
    congr 1
    rw [pglFixedCorrection_mul K L hn X hX]
    simp only [map_inv, _root_.mul_inv_rev]
    rfl

/-- A projective linear coordinate change over a finite Galois extension
which is fixed by every automorphism already comes from the ground field. -/
theorem pgl_fixed_descends
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {n : ℕ} (hn : n ≠ 0)
    (x : PGL(Fin n, L))
    (hx : ∀ σ : Gal(L/K),
      Matrix.ProjGenLinGroup.map (galFieldAction K L σ).toRingHom x = x) :
    ∃ y : PGL(Fin n, K),
      Matrix.ProjGenLinGroup.map (algebraMap K L) y = x := by
  induction x using Matrix.ProjGenLinGroup.induction_on with
  | mk X =>
      have hX (σ : Gal(L/K)) :
          Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.map (galFieldAction K L σ).toRingHom X) =
            Matrix.ProjGenLinGroup.mk X := by
        simpa only [Matrix.ProjGenLinGroup.map_mk] using hx σ
      let a := pglFixedScalarCocycle K L hn X hX
      obtain ⟨V, hV⟩ :=
        a.isCoboundary_of_galois_of_ne_zero K L (by omega)
      let u : Gal(L/K) → Lˣ := pglFixedCorrection K L X hX
      let v : Lˣ := V.det
      have hv (σ : Gal(L/K)) :
          Units.map (galFieldAction K L σ).toRingHom.toMonoidHom v = v * (u σ)⁻¹ := by
        have hdet := congrArg Matrix.GeneralLinearGroup.det (hV σ)
        have hdet' : (u σ)⁻¹ = v⁻¹ *
            Units.map (galFieldAction K L σ).toRingHom.toMonoidHom v := by
          simpa [a, pglFixedScalarCocycle, v,
            Matrix.GeneralLinearGroup.det_scalar,
            Matrix.GeneralLinearGroup.map_det] using hdet
        symm
        calc
          v * (u σ)⁻¹ = v * (v⁻¹ *
              Units.map (galFieldAction K L σ).toRingHom.toMonoidHom v) := by rw [hdet']
          _ = (v * v⁻¹) *
              Units.map (galFieldAction K L σ).toRingHom.toMonoidHom v := by rw [mul_assoc]
          _ = Units.map (galFieldAction K L σ).toRingHom.toMonoidHom v := by simp
      have hspec (σ : Gal(L/K)) :
          Matrix.GeneralLinearGroup.map (galFieldAction K L σ).toRingHom X *
            Matrix.GeneralLinearGroup.scalar (Fin n) (u σ) = X :=
        pglFixedCorrection_spec K L X hX σ
      have hXmap (σ : Gal(L/K)) :
          Matrix.GeneralLinearGroup.map (galFieldAction K L σ).toRingHom X =
            X * Matrix.GeneralLinearGroup.scalar (Fin n) (u σ)⁻¹ := by
        apply mul_right_cancel (b := Matrix.GeneralLinearGroup.scalar (Fin n) (u σ))
        rw [hspec σ]
        symm
        calc
          (X * Matrix.GeneralLinearGroup.scalar (Fin n) (u σ)⁻¹) *
              Matrix.GeneralLinearGroup.scalar (Fin n) (u σ) =
              X * (Matrix.GeneralLinearGroup.scalar (Fin n) (u σ)⁻¹ *
                Matrix.GeneralLinearGroup.scalar (Fin n) (u σ)) := by rw [mul_assoc]
          _ = X := by
            rw [← (Matrix.GeneralLinearGroup.scalar (Fin n)).map_mul]
            simp
      let Z : GL (Fin n) L := X * Matrix.GeneralLinearGroup.scalar (Fin n) v⁻¹
      have hZ (σ : Gal(L/K)) :
          Matrix.GeneralLinearGroup.map (galFieldAction K L σ).toRingHom Z = Z := by
        dsimp only [Z]
        rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_scalar, hXmap σ]
        calc
          (X * Matrix.GeneralLinearGroup.scalar (Fin n) (u σ)⁻¹) *
              Matrix.GeneralLinearGroup.scalar (Fin n)
                (Units.map (galFieldAction K L σ).toRingHom.toMonoidHom v⁻¹) =
              X * (Matrix.GeneralLinearGroup.scalar (Fin n) (u σ)⁻¹ *
                Matrix.GeneralLinearGroup.scalar (Fin n)
                  (Units.map (galFieldAction K L σ).toRingHom.toMonoidHom v⁻¹)) := by
                rw [mul_assoc]
          _ = X * Matrix.GeneralLinearGroup.scalar (Fin n)
                ((u σ)⁻¹ * Units.map (galFieldAction K L σ).toRingHom.toMonoidHom v⁻¹) := by
                rw [← (Matrix.GeneralLinearGroup.scalar (Fin n)).map_mul]
          _ = X * Matrix.GeneralLinearGroup.scalar (Fin n) v⁻¹ := by
                congr 2
                rw [map_inv, hv σ, _root_.mul_inv_rev]
                simp only [inv_inv]
                rw [← mul_assoc, inv_mul_cancel, one_mul]
      have hZentry (σ : Gal(L/K)) (i j : Fin n) :
          σ ((Z : Matrix (Fin n) (Fin n) L) i j) = Z i j := by
        have h := congrArg (fun q : GL (Fin n) L =>
          (q : Matrix (Fin n) (Fin n) L)) (hZ σ)
        have hij := congrFun (congrFun h i) j
        change (galFieldAction K L σ).toRingHom ((Z : Matrix (Fin n) (Fin n) L) i j) = Z i j
        simpa only [Matrix.GeneralLinearGroup.map_apply] using hij
      obtain ⟨C, hC⟩ := exists_matrix_of_galois_fixed K L
        (Z : Matrix (Fin n) (Fin n) L) hZentry
      have hZdet : (Z : Matrix (Fin n) (Fin n) L).det ≠ 0 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply Z]
        exact Units.ne_zero Z.det
      have hCdet : C.det ≠ 0 := matrix_det_ne_zero_of_map_eq K L C
        (Z : Matrix (Fin n) (Fin n) L) hC hZdet
      let Y : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero C hCdet
      have hY : Matrix.GeneralLinearGroup.map (algebraMap K L) Y = Z := by
        apply Units.ext
        change C.map (algebraMap K L) = (Z : Matrix (Fin n) (Fin n) L)
        exact hC
      refine ⟨Matrix.ProjGenLinGroup.mk Y, ?_⟩
      rw [Matrix.ProjGenLinGroup.map_mk, hY]
      dsimp only [Z]
      rw [Matrix.ProjGenLinGroup.mk.map_mul,
        Matrix.ProjGenLinGroup.mk_scalar, mul_one]

end PfaffianDescent.QuarticNet.ProjectiveCocycle

import AllCharacteristics.TangentHyperplaneGeneric
import PfaffianDescent.CubicLineResidualTransversality

/-!
# Kollár's universal affine line through a normalized cubic point

This is the first coordinate layer of Kollár's explicit unirationality
construction.  With a smooth point normalized to the first coordinate vertex,
the universal affine line has direction `(0, u₁, u₂, 1)`.  Its residual
quadratic has no zero parameter at its generic roots whenever the selected
linear derivative is nonzero.
-/

namespace AllCharacteristics

open AlgebraicGeometry HomogeneousProjective
open PfaffianDescent MvPolynomial

universe u

/-- The normalized projective base point of Kollár's affine construction. -/
def kollarBasePoint (R : Type*) [Zero R] [One R] : Fin 4 → R := ![1, 0, 0, 0]

/-- The affine direction chart on the projective space of lines through the
normalized base point. -/
def kollarAffineLineDirection (R : Type*) [Zero R] [One R]
    (u : Fin 2 → R) : Fin 4 → R := ![0, u 0, u 1, 1]

/-- The universal direction in the affine chart of lines through the base
point. -/
noncomputable def kollarUniversalLineDirection (K : Type u) [CommRing K] :
    Fin 4 → MvPolynomial (Fin 2) K :=
  kollarAffineLineDirection _ (fun i => X i)

theorem eval_kollarUniversalLineDirection_at_zero
    (K : Type u) [CommRing K] :
    (fun i => MvPolynomial.eval (fun _ : Fin 2 => (0 : K))
      (kollarUniversalLineDirection K i)) =
      kollarAffineLineDirection K (fun _ => 0) := by
  funext i
  fin_cases i <;> simp [kollarUniversalLineDirection, kollarAffineLineDirection]

/-- If the derivative in the last affine direction at the normalized point is
nonzero, then the universal line is not tangent at the base point.  Thus every
residual root has nonzero line parameter. -/
theorem kollar_universal_line_secantCoefficient_ne_zero
    {K : Type u} [Field K] (c : Cubic K 4)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    (c.map (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K)).mixed
      (fun i => MvPolynomial.C (kollarBasePoint K i))
      (kollarUniversalLineDirection K) ≠ 0 := by
  let R := MvPolynomial (Fin 2) K
  let e : R →+* K := MvPolynomial.eval (fun _ : Fin 2 => (0 : K))
  let cR : Cubic R 4 := c.map MvPolynomial.C
  let pR : Fin 4 → R := fun i => MvPolynomial.C (kollarBasePoint K i)
  let dR : Fin 4 → R := kollarUniversalLineDirection K
  have hc : cR.map e = c := by
    funext i
    dsimp [cR, e, Cubic.map]
    exact MvPolynomial.eval_C _
  have hp : (fun i => e (pR i)) = kollarBasePoint K := by
    funext i
    dsimp [pR, e]
    exact MvPolynomial.eval_C _
  have hd : (fun i => e (dR i)) =
      kollarAffineLineDirection K (fun _ => 0) := by
    exact eval_kollarUniversalLineDirection_at_zero K
  intro hzero
  apply hsec
  change cR.mixed pR dR = 0 at hzero
  have hmap := Cubic.mixed_map e cR pR dR
  rw [hc, hp, hd] at hmap
  rw [hmap, hzero]
  rfl

/-- The preceding coefficient remains nonzero at the generic affine line
direction. -/
theorem kollar_generic_line_secantCoefficient_ne_zero
    {K : Type u} [Field K] (c : Cubic K 4)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)))).mixed
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
        (kollarBasePoint K i))
      (fun i => algebraMap (MvPolynomial (Fin 2) K)
        (FractionRing (MvPolynomial (Fin 2) K))
        (kollarUniversalLineDirection K i)) ≠ 0 := by
  let R := MvPolynomial (Fin 2) K
  let L := FractionRing R
  let cR : Cubic R 4 := c.map MvPolynomial.C
  let pR : Fin 4 → R := fun i => MvPolynomial.C (kollarBasePoint K i)
  let dR : Fin 4 → R := kollarUniversalLineDirection K
  have hR : cR.mixed pR dR ≠ 0 :=
    kollar_universal_line_secantCoefficient_ne_zero c hsec
  intro hzero
  apply hR
  apply IsFractionRing.injective R L
  have hmap := Cubic.mixed_map (algebraMap R L) cR pR dR
  have hc : cR.map (algebraMap R L) =
      c.map (algebraMap K L) := by
    funext i
    change (algebraMap R L) ((algebraMap K R) (c i)) =
      (algebraMap K L) (c i)
    exact IsScalarTower.algebraMap_apply K R L (c i)
  have hp : (fun i => algebraMap R L (pR i)) =
      fun i => algebraMap K L (kollarBasePoint K i) := by
    funext i
    change (algebraMap R L) ((algebraMap K R) (kollarBasePoint K i)) =
      (algebraMap K L) (kollarBasePoint K i)
    exact IsScalarTower.algebraMap_apply K R L (kollarBasePoint K i)
  have hd : (fun i => algebraMap R L (dR i)) =
      fun i => algebraMap R L (kollarUniversalLineDirection K i) := rfl
  rw [hc, hp, hd, hzero] at hmap
  simpa only [map_zero] using hmap.symm

/-- The normal vector of the plane of directions through the normalized
base point.  Its parametrized hyperplane is the projective plane `x₀ = 0`. -/
def kollarDirectionPlaneNormal (K : Type u) [Zero K] [One K] : Fin 4 → K :=
  ![1, 0, 0, 0]

/-- Homogeneous coordinates for the projective space of lines through the
normalized base point. -/
noncomputable def kollarProjectiveLinePolynomialDirection
    (K : Type u) [Field K] : Fin 4 → MvPolynomial (Fin 3) K :=
  ((hyperplaneInclusion (kollarDirectionPlaneNormal K) 0).map MvPolynomial.C).mulVec
    (fun j => MvPolynomial.X j)

/-- In the standard chart, the parametrized direction plane has coordinates
`(0,u₀,u₁,u₂)`. -/
theorem kollarProjectiveLinePolynomialDirection_eq_standard
    (K : Type u) [Field K] :
    kollarProjectiveLinePolynomialDirection K =
      ![0, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2] := by
  funext i
  fin_cases i <;>
    simp [kollarProjectiveLinePolynomialDirection, kollarDirectionPlaneNormal,
      hyperplaneInclusion, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The generic projective line through the normalized base point. -/
noncomputable def kollarGenericProjectiveLineDirection
    (K : Type u) [Field K] : Fin 4 → FractionRing (MvPolynomial (Fin 3) K) :=
  fun i => algebraMap (MvPolynomial (Fin 3) K)
    (FractionRing (MvPolynomial (Fin 3) K))
      (kollarProjectiveLinePolynomialDirection K i)

/-- At the third coordinate vertex of the direction plane, the homogeneous
universal line is the last affine coordinate direction. -/
theorem eval_kollarProjectiveLinePolynomialDirection_at_last
    (K : Type u) [Field K] :
    (fun i => MvPolynomial.eval (![0, 0, 1] : Fin 3 → K)
      (kollarProjectiveLinePolynomialDirection K i)) =
      kollarAffineLineDirection K (fun _ => 0) := by
  funext i
  fin_cases i <;>
    simp [kollarProjectiveLinePolynomialDirection, kollarDirectionPlaneNormal,
      kollarAffineLineDirection, hyperplaneInclusion, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- The homogeneous universal line retains the nonzero secant coefficient at
the normalized point. -/
theorem kollar_projective_line_secantCoefficient_ne_zero
    {K : Type u} [Field K] (c : Cubic K 4)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    (c.map (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)).mixed
      (fun i => MvPolynomial.C (kollarBasePoint K i))
      (kollarProjectiveLinePolynomialDirection K) ≠ 0 := by
  let R := MvPolynomial (Fin 3) K
  let e : R →+* K := MvPolynomial.eval (![0, 0, 1] : Fin 3 → K)
  let cR : Cubic R 4 := c.map MvPolynomial.C
  let pR : Fin 4 → R := fun i => MvPolynomial.C (kollarBasePoint K i)
  let dR : Fin 4 → R := kollarProjectiveLinePolynomialDirection K
  have hc : cR.map e = c := by
    funext i
    dsimp [cR, e, Cubic.map]
    exact MvPolynomial.eval_C _
  have hp : (fun i => e (pR i)) = kollarBasePoint K := by
    funext i
    dsimp [pR, e]
    exact MvPolynomial.eval_C _
  have hd : (fun i => e (dR i)) =
      kollarAffineLineDirection K (fun _ => 0) := by
    exact eval_kollarProjectiveLinePolynomialDirection_at_last K
  intro hzero
  apply hsec
  change cR.mixed pR dR = 0 at hzero
  have hmap := Cubic.mixed_map e cR pR dR
  rw [hc, hp, hd] at hmap
  rw [hmap, hzero]
  rfl

/-- The generic projective line through the normalized point has nonzero
secant coefficient. -/
theorem kollar_generic_projective_line_secantCoefficient_ne_zero
    {K : Type u} [Field K] (c : Cubic K 4)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).mixed
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K))
        (kollarBasePoint K i))
      (kollarGenericProjectiveLineDirection K) ≠ 0 := by
  let R := MvPolynomial (Fin 3) K
  let L := FractionRing R
  let cR : Cubic R 4 := c.map MvPolynomial.C
  let pR : Fin 4 → R := fun i => MvPolynomial.C (kollarBasePoint K i)
  let dR : Fin 4 → R := kollarProjectiveLinePolynomialDirection K
  have hR : cR.mixed pR dR ≠ 0 :=
    kollar_projective_line_secantCoefficient_ne_zero c hsec
  intro hzero
  apply hR
  apply IsFractionRing.injective R L
  have hmap := Cubic.mixed_map (algebraMap R L) cR pR dR
  have hc : cR.map (algebraMap R L) =
      c.map (algebraMap K L) := by
    funext i
    change (algebraMap R L) ((algebraMap K R) (c i)) =
      (algebraMap K L) (c i)
    exact IsScalarTower.algebraMap_apply K R L (c i)
  have hp : (fun i => algebraMap R L (pR i)) =
      fun i => algebraMap K L (kollarBasePoint K i) := by
    funext i
    change (algebraMap R L) ((algebraMap K R) (kollarBasePoint K i)) =
      (algebraMap K L) (kollarBasePoint K i)
    exact IsScalarTower.algebraMap_apply K R L (kollarBasePoint K i)
  have hd : (fun i => algebraMap R L (dR i)) =
      kollarGenericProjectiveLineDirection K := rfl
  rw [hc, hp, hd, hzero] at hmap
  simpa only [map_zero] using hmap.symm

/-- A nonzero first derivative at the normalized point forces the cubic
equation itself to be nonzero. -/
theorem kollar_equation_ne_zero_of_secantCoefficient_ne_zero
    {K : Type u} [Field K] (c : Cubic K 4)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    c.toMvPolynomial ≠ 0 := by
  intro hzero
  apply hsec
  rw [Cubic.mixed_eq_sum_pderiv_eval, hzero]
  simp

/-- The generic projective line through the normalized point is not contained
in a smooth cubic surface. -/
theorem kollar_generic_projective_line_eval_ne_zero_of_smooth
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)]
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).eval
      (kollarGenericProjectiveLineDirection K) ≠ 0 := by
  let R := MvPolynomial (Fin 3) K
  let L := FractionRing R
  let g : Fin 4 → K := kollarDirectionPlaneNormal K
  have hg : g 0 ≠ 0 := by
    simp [g, kollarDirectionPlaneNormal]
  have hF0 : F ≠ 0 := by
    rw [← hc]
    exact kollar_equation_ne_zero_of_secantCoefficient_ne_zero c hsec
  have hprime : (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic F hF hF0
  have hrestF : rectangularSubstitution (hyperplaneInclusion g 0) F ≠ 0 :=
    hyperplane_restriction_ne_zero_of_prime F hF hF0 hprime g 0 hg
  have hrest : rectangularSubstitution (hyperplaneInclusion g 0)
      c.toMvPolynomial ≠ 0 := by
    rw [hc]
    exact hrestF
  have hd : kollarGenericProjectiveLineDirection K =
      genericHyperplaneDirection g 0 := by
    funext i
    simp only [kollarGenericProjectiveLineDirection,
      kollarProjectiveLinePolynomialDirection, genericHyperplaneDirection, g]
    rw [Matrix.mulVec, Matrix.mulVec]
    simp only [dotProduct]
    rw [_root_.map_sum]
    simp only [Matrix.map_apply, map_mul]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
  rw [hd, cubic_eval_genericHyperplaneDirection]
  intro hzero
  apply hrest
  apply IsFractionRing.injective R L
  simpa using hzero

/-- The generic line through a normalized smooth cubic point has the expected
genuine quadratic residual polynomial.  The remaining condition for the
quadratic-pair construction is its irreducibility. -/
theorem kollar_generic_projective_line_residual_data_of_smooth
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)]
    (hpoint : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).eval
        (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K))
          (kollarBasePoint K i)) = 0 ∧
    (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).mixed
        (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K))
          (kollarBasePoint K i))
        (kollarGenericProjectiveLineDirection K) ≠ 0 ∧
    (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).eval
        (kollarGenericProjectiveLineDirection K) ≠ 0 ∧
    (Cubic.lineResidualPolynomial
      (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K))))
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K))
        (kollarBasePoint K i))
      (kollarGenericProjectiveLineDirection K)).natDegree = 2 := by
  let L := FractionRing (MvPolynomial (Fin 3) K)
  let cL : Cubic L 4 := c.map (algebraMap K L)
  let pL : Fin 4 → L := fun i => algebraMap K L (kollarBasePoint K i)
  let dL : Fin 4 → L := kollarGenericProjectiveLineDirection K
  have hpL : cL.eval pL = 0 := by
    rw [Cubic.eval_map]
    simp [hpoint]
  have hsecL : cL.mixed pL dL ≠ 0 := by
    exact kollar_generic_projective_line_secantCoefficient_ne_zero c hsec
  have hdirL : cL.eval dL ≠ 0 := by
    exact kollar_generic_projective_line_eval_ne_zero_of_smooth F hF c hc hsec
  refine ⟨hpL, hsecL, hdirL, ?_⟩
  exact Cubic.lineResidualPolynomial_natDegree_eq_two cL pL dL hdirL

end AllCharacteristics

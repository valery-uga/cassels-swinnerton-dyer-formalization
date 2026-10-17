import AllCharacteristics.SmoothCubicTangent
import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-!
# Generic tangent-hyperplane directions on a smooth cubic surface

The tangent hyperplane at a smooth cubic point is parametrized by three
homogeneous coordinates.  Its generic point has nonzero cubic value, because
an integral cubic surface cannot contain a hyperplane.  This supplies the
nonvanishing input for residual tangent constructions over a function field.
-/

namespace PfaffianDescent
namespace Cubic

open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- Passing a cubic tensor through a coefficient homomorphism commutes with
its associated multivariate polynomial. -/
theorem toMvPolynomial_map (f : R →+* S) (c : Cubic R n) :
    (c.map f).toMvPolynomial = c.toMvPolynomial.map f := by
  unfold toMvPolynomial map
  symm
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

end Cubic
end PfaffianDescent

namespace AllCharacteristics

open PfaffianDescent MvPolynomial
open scoped BigOperators

universe u

/-- After a coefficient extension, the mixed cubic form at a base-field point
is the gradient pairing with the extended direction. -/
lemma mixed_map_eq_gradient_dot
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (c : Cubic K 4) (p : Fin 4 → K) (d : Fin 4 → L) :
    (c.map f).mixed (fun i ↦ f (p i)) d =
      ∑ i, d i * f ((MvPolynomial.pderiv i c.toMvPolynomial).eval p) := by
  rw [Cubic.mixed_eq_sum_pderiv_eval]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Cubic.toMvPolynomial_map, MvPolynomial.pderiv_map]
  let q := MvPolynomial.pderiv i c.toMvPolynomial
  have he : MvPolynomial.eval₂Hom f (fun j ↦ f (p j)) =
      f.comp (MvPolynomial.eval p) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro j
      simp
  rw [MvPolynomial.eval_map]
  exact DFunLike.congr_fun he q

/-- The explicit parametrization of a hyperplane lies in the tangent
hyperplane determined by the gradient vector. -/
lemma mixed_hyperplaneInclusion_zero
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (c : Cubic K 4) (p : Fin 4 → K)
    (g : Fin 4 → K)
    (hg : ∀ i, g i = (MvPolynomial.pderiv i c.toMvPolynomial).eval p)
    (k : Fin 4) (hk : g k ≠ 0) (x : Fin 3 → L) :
    (c.map f).mixed (fun i ↦ f (p i))
      (((hyperplaneInclusion g k).map f).mulVec x) = 0 := by
  rw [mixed_map_eq_gradient_dot]
  simp_rw [← hg]
  simpa [mul_comm] using hyperplaneInclusion_dot_mulVec_zero f g k hk x

/-- Generic homogeneous coordinates in the explicit parametrization of a
hyperplane. -/
noncomputable def genericHyperplaneDirection
    {K : Type u} [Field K] (g : Fin 4 → K) (k : Fin 4) :
    Fin 4 → FractionRing (MvPolynomial (Fin 3) K) :=
  ((hyperplaneInclusion g k).map
    (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).mulVec
      (fun j ↦ algebraMap (MvPolynomial (Fin 3) K)
        (FractionRing (MvPolynomial (Fin 3) K)) (MvPolynomial.X j))

/-- Evaluating a cubic at the generic hyperplane coordinates is its explicit
hyperplane restriction, viewed in the function field of the parameters. -/
theorem cubic_eval_genericHyperplaneDirection
    {K : Type u} [Field K] (c : Cubic K 4) (g : Fin 4 → K) (k : Fin 4) :
    (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).eval
      (genericHyperplaneDirection g k) =
    algebraMap (MvPolynomial (Fin 3) K) (FractionRing (MvPolynomial (Fin 3) K))
      (rectangularSubstitution (hyperplaneInclusion g k) c.toMvPolynomial) := by
  let R := MvPolynomial (Fin 3) K
  let L := FractionRing R
  let M := hyperplaneInclusion g k
  let d : Fin 4 → L := genericHyperplaneDirection g k
  have hcomp : MvPolynomial.eval₂Hom (algebraMap K L) d =
      (algebraMap R L).comp (rectangularSubstitution M).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      change algebraMap K L r = algebraMap R L (rectangularSubstitution M (MvPolynomial.C r))
      have hM : rectangularSubstitution M (MvPolynomial.C r) = MvPolynomial.C r := by
        simpa only [MvPolynomial.algebraMap_eq] using (rectangularSubstitution M).commutes r
      rw [hM]
      exact (IsScalarTower.algebraMap_apply K R L r).symm
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change d i = algebraMap R L (rectangularSubstitution M (MvPolynomial.X i))
      rw [rectangularSubstitution_X]
      simp only [d, genericHyperplaneDirection, M, rectangularLinearCoordinate,
        Matrix.mulVec, dotProduct, Matrix.map_apply]
      rw [_root_.map_sum]
      simp only [map_mul]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
  change (c.map (algebraMap K L)).eval d =
    algebraMap R L (rectangularSubstitution M c.toMvPolynomial)
  rw [← Cubic.eval_toMvPolynomial]
  exact DFunLike.congr_fun hcomp c.toMvPolynomial

end AllCharacteristics

namespace AllCharacteristics

open AlgebraicGeometry
open HomogeneousProjective
open PfaffianDescent MvPolynomial

universe u

/-- On a smooth cubic surface, the generic point of the tangent hyperplane has
nonzero cubic value.  This is the generic nonvanishing ingredient for the
residual tangent construction. -/
theorem exists_generic_tangent_direction_of_smooth
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    (p : Fin 4 → K) (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ d : Fin 4 → FractionRing (MvPolynomial (Fin 3) K),
      (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).mixed
        (fun i ↦ algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (p i)) d = 0 ∧
      (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).eval d ≠ 0 := by
  classical
  obtain ⟨hp0, hp, k, hk⟩ := hs
  let g : Fin 4 → K := fun i ↦ (MvPolynomial.pderiv i c.toMvPolynomial).eval p
  have hg : ∀ i, g i = (MvPolynomial.pderiv i c.toMvPolynomial).eval p := by
    intro i
    rfl
  have hgk : g k ≠ 0 := by
    simpa only [g] using hk
  have hF0 : F ≠ 0 := by
    intro hzero
    apply hk
    rw [hc, hzero]
    simp
  have hprime : (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic F hF hF0
  have hrestF : rectangularSubstitution (hyperplaneInclusion g k) F ≠ 0 :=
    hyperplane_restriction_ne_zero_of_prime F hF hF0 hprime g k hgk
  have hrest : rectangularSubstitution (hyperplaneInclusion g k) c.toMvPolynomial ≠ 0 := by
    rw [hc]
    exact hrestF
  let R := MvPolynomial (Fin 3) K
  let L := FractionRing R
  let d : Fin 4 → L := genericHyperplaneDirection g k
  refine ⟨d, ?_, ?_⟩
  · exact mixed_hyperplaneInclusion_zero (algebraMap K L) c p g hg k hgk
      (fun j ↦ algebraMap R L (MvPolynomial.X j))
  · rw [show d = genericHyperplaneDirection g k by rfl,
      cubic_eval_genericHyperplaneDirection]
    intro h
    apply hrest
    apply IsFractionRing.injective R L
    simpa using h

/-- The generic tangent direction gives nonzero homogeneous coordinates for
its residual point on a smooth cubic surface. -/
theorem exists_generic_nonzero_tangentResidual_of_smooth
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    (p : Fin 4 → K) (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ d : Fin 4 → FractionRing (MvPolynomial (Fin 3) K),
      Cubic.tangentResidualPoint
        (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K))))
        (fun i ↦ algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (p i)) d ≠ 0 ∧
      (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).eval
        (Cubic.tangentResidualPoint
          (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K))))
          (fun i ↦ algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (p i)) d) = 0 := by
  let R := MvPolynomial (Fin 3) K
  let L := FractionRing R
  obtain ⟨d, htan, hdeval⟩ :=
    exists_generic_tangent_direction_of_smooth F hF c hc p hs
  have hp : c.eval p = 0 := by
    have h := hs.2.1
    change MvPolynomial.eval₂ (RingHom.id K) p c.toMvPolynomial = 0 at h
    rw [Cubic.eval_toMvPolynomial] at h
    exact h
  refine ⟨d, ?_, ?_⟩
  · apply Cubic.tangentResidualPoint_ne_zero_of_eval_ne_zero
    · intro h
      apply hs.1
      funext i
      apply (algebraMap K L).injective
      simpa using congrFun h i
    · rw [Cubic.eval_map, hp, map_zero]
    · exact hdeval
  · exact Cubic.eval_tangentResidualPoint _ _ _ (by
      rw [Cubic.eval_map, hp, map_zero]) htan

end AllCharacteristics

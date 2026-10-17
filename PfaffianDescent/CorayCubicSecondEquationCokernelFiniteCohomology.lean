import PfaffianDescent.CorayHypersurfaceTwistAmbientFiniteCohomology
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import PfaffianDescent.ClosedImmersionPushforwardExact

/-! The ORIGINAL q on the ORIGINAL smooth cubic quotient gives a genuine
injective sheaf map and canonical short exact cokernel sequence. Ambient H¹
of its actual pushed-forward cokernel is finite over the ORIGINAL K.
Its identification with the literal p/q curve and intrinsic H¹ remains open.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal original q class, in its actual homogeneous component of
the literal original cubic quotient. No alternate equation or scalar action. -/
def cubicSecondEquationHomogeneous
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n) : grading (equationIdeal p hp) n :=
  ⟨(quotientGradedRingHom (equationIdeal p hp)) q,
    (quotientGradedRingHom (equationIdeal p hp)).map_mem hq⟩

/-- The original nonmembership hypothesis supplies the actual nonzero q
class in the cubic coordinate ring. No nonvanishing certificate is supplied. -/
theorem cubicSecondEquationHomogeneous_ne_zero
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    (cubicSecondEquationHomogeneous p q hp n hq : CoordinateRing (equationIdeal p hp)) ≠ 0 := by
  change Ideal.Quotient.mk (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) q ≠ 0
  intro hz
  exact hnot (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- Genuine Mono of the ACTUAL original q multiplication on the ACTUAL
smooth cubic twist. Smoothness internally supplies the actual domain. -/
theorem cubicSecondEquation_mulHomogeneous_mono
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (m : ℕ) :
    Mono (mulHomogeneous (grading (equationIdeal p hp))
      (cubicSecondEquationHomogeneous p q hp n hq) m) := by
  letI : (equationIdeal p hp).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := inferInstance
  exact mulHomogeneous_mono (grading (equationIdeal p hp))
    (cubicSecondEquationHomogeneous p q hp n hq)
    (cubicSecondEquationHomogeneous_ne_zero p q hp n hq hnot) m

/-- The genuine canonical q-cokernel sequence on the original cubic is
short exact. Its third term is explicitly the ACTUAL cokernel, not an assumed
identification with the original p/q curve's pushed-forward unit. -/
theorem cubicSecondEquation_homogeneousRestrictionSequence_shortExact
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (m : ℕ) :
    (homogeneousRestrictionSequence (grading (equationIdeal p hp))
      (cubicSecondEquationHomogeneous p q hp n hq) m).ShortExact := by
  letI : (equationIdeal p hp).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := inferInstance
  exact homogeneousRestrictionSequence_shortExact (grading (equationIdeal p hp))
    (cubicSecondEquationHomogeneous p q hp n hq)
    (cubicSecondEquationHomogeneous_ne_zero p q hp n hq hnot) m

/-- The SAME actual q-cokernel sequence stays short exact after the actual
closed cubic pushforward; its exactness is derived by genuine stalk proofs. -/
theorem cubicSecondEquation_pushforwardRestrictionSequence_shortExact
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (m : ℕ) :
    ((homogeneousRestrictionSequence (grading (equationIdeal p hp))
      (cubicSecondEquationHomogeneous p q hp n hq) m).map
        (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp))).ShortExact := by
  exact schemeModulePushforward_map_shortExact_of_closedImmersion
    (hypersurfaceToAmbient p hp)
    (homogeneousRestrictionSequence (grading (equationIdeal p hp))
      (cubicSecondEquationHomogeneous p q hp n hq) m)
    (cubicSecondEquation_homogeneousRestrictionSequence_shortExact p q hp hp0 n hq hnot m)

/-- Isolate the native finite-cohomology calculation from smoothness and
chosen injective/Ext infrastructure. The private geometric caller supplies
short exactness of precisely this pushed multiplication cokernel sequence. -/
private theorem cubicSecondEquation_cokernelPushforward_cohomology_one_finite_core
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    {n : ℕ} (s : grading (equationIdeal p hp) n) (m : ℕ)
    (hT : ((homogeneousRestrictionSequence (grading (equationIdeal p hp)) s m).map
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp))).ShortExact) :
    let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    letI : Linear K P.Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K (schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp)) s m))) 1) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  letI : Linear K P.Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  let R := homogeneousRestrictionSequence (grading (equationIdeal p hp)) s m
  let T := R.map (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp))
  letI : Subsingleton (schemeModuleCohomology P T.X₂ 1) :=
    p3HypersurfaceTwistPushforward_cohomology_one_subsingleton K p hp hp0 m
  have hfinite : Module.Finite K (schemeModuleCohomology P T.X₁ 2) :=
    p3HypersurfaceTwistPushforward_cohomology_two_finite K p hp hp0 (m + n)
  exact schemeModuleRestriction_rightCohomology_finite_of_middle_zero_and_next_left_finite
    (ambientToBase (R := K) (σ := Fin 4)) T hT 1 hfinite

/-- Finite ORIGINAL-K ambient H¹ of the ACTUAL q-cokernel pushforward,
for every m and original q degree n. All geometric regularity, short exactness,
ambient cohomology/Ext inputs and scalar actions are discharged internally.
This is not yet intrinsic H¹ of the literal projective p/q curve. -/
theorem cubicSecondEquation_cokernelPushforward_cohomology_one_finite_native
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (m : ℕ) :
    let PS := MvPolynomial.homogeneousSubmodule (Fin 4) K
    let P := Proj PS
    let D := cokernel (mulHomogeneous (grading (equationIdeal p hp))
      (cubicSecondEquationHomogeneous p q hp n hq) m)
    letI : EnoughInjectives P.Modules := sheafOfModules_enoughInjectives P.ringCatSheaf
    letI : HasExt.{u} P.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} P.Modules
    letI : Linear K P.Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K (schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj D) 1) := by
  let PS := MvPolynomial.homogeneousSubmodule (Fin 4) K
  let P := Proj PS
  letI : EnoughInjectives P.Modules := sheafOfModules_enoughInjectives P.ringCatSheaf
  letI : HasExt.{u} P.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} P.Modules
  letI : Linear K P.Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  letI : (equationIdeal p hp).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := inferInstance
  exact cubicSecondEquation_cokernelPushforward_cohomology_one_finite_core
    p hp hp0 (cubicSecondEquationHomogeneous p q hp n hq) m
    (cubicSecondEquation_pushforwardRestrictionSequence_shortExact p q hp hp0 n hq hnot m)

end PfaffianDescent.Coray

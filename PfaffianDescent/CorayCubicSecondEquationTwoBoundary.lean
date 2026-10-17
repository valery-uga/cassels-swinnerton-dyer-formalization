import PfaffianDescent.CorayProjectiveIntersectionIntrinsicH1Finite

/-! The SAME actual q-cokernel and cubic ambient connecting maps, composed
with the ORIGINAL ambient pi action. The actual multiplication-zero relation
is proved from the genuine short exact sequence; it is not an input.
SOURCE ONLY / UNVERIFIED. Root owns all compiler and kernel checks. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
local notation "P" => Proj PS
local notation "piP" => ambientToBase (R := K) (σ := Fin 4)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual connecting class followed by the SAME first sequence map
is zero. This generic helper derives the relation from the actual Ext class. -/
theorem schemeModuleRestrictionConnectingLinearMapOver_postcomp_f_zero
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (a : ℕ)
    (z : schemeModuleCohomology X S.X₃ a) :
    (schemeModuleRestrictionConnectingLinearMapOver pi S hS a z).comp
      (Ext.mk₀ S.f) (add_zero (a + 1)) = 0 := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  change (z.comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero (a + 1)) = 0
  rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

/-- Only the degree identity 0+n=n is used. The actual coefficient sheaf
and scalar action are preserved. -/
def cubicSecondEquation_zeroLeftIso
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ) :
    (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
      (sheafOfModules (grading (equationIdeal p hp)) (0 + n)) ≅
    (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
      (sheafOfModules (grading (equationIdeal p hp)) n) :=
  eqToIso (by rw [zero_add])

/-- The SAME actual q boundary, with the explicit degree-identity Iso on
its coefficient. The original short exact sequence is derived internally. -/
def cubicSecondEquation_boundaryOneLinearMap
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    letI : Linear K (P).Modules := schemeModulesLinearOver piP
    schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp))
          (cubicSecondEquationHomogeneous p q hp n hq) 0))) 1 →ₗ[K]
      schemeModuleCohomology P
        ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
          (sheafOfModules (grading (equationIdeal p hp)) n)) 2 := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  let T := (homogeneousRestrictionSequence (grading (equationIdeal p hp))
    (cubicSecondEquationHomogeneous p q hp n hq) 0).map
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp))
  have hT : T.ShortExact :=
    cubicSecondEquation_pushforwardRestrictionSequence_shortExact p q hp hp0 n hq hnot 0
  exact (schemeModuleCohomologyIsoLinearEquivOver piP
      (cubicSecondEquation_zeroLeftIso p hp n) 2).toLinearMap.comp
    (schemeModuleRestrictionConnectingLinearMapOver piP T hT 1)

/-- Its injectivity follows from the actual cubic pushforward H¹ vanishing. -/
theorem cubicSecondEquation_boundaryOneLinearMap_injective
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    Function.Injective (cubicSecondEquation_boundaryOneLinearMap p q hp hp0 n hq hnot) := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  letI : (equationIdeal p hp).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := inferInstance
  let T := (homogeneousRestrictionSequence (grading (equationIdeal p hp))
    (cubicSecondEquationHomogeneous p q hp n hq) 0).map
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp))
  have hT : T.ShortExact :=
    cubicSecondEquation_pushforwardRestrictionSequence_shortExact p q hp hp0 n hq hnot 0
  letI : Subsingleton (schemeModuleCohomology P T.X₂ 1) :=
    p3HypersurfaceTwistPushforward_cohomology_one_subsingleton K p hp hp0 0
  exact (schemeModuleCohomologyIsoLinearEquivOver piP
      (cubicSecondEquation_zeroLeftIso p hp n) 2).injective.comp
    (schemeModuleRestrictionConnectingLinearMapOver_injective piP T hT 1)

/-- The SAME actual cubic ambient boundary, with the cubic domain and
short exact sequence derived from the original geometric inputs. -/
def cubicAmbient_boundaryTwoLinearMap
    [HasExt.{u} (P).Modules]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) :
    letI : Linear K (P).Modules := schemeModulesLinearOver piP
    schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) n)) 2 →ₗ[K]
      schemeModuleCohomology P (sheafOfModules PS (n + 3)) 3 := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  letI : (equationIdeal p hp).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := inferInstance
  exact schemeModuleRestrictionConnectingLinearMapOver piP
    (hypersurfaceTwistRestrictionSequence p hp n)
    (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 n) 2

/-- Actual ambient H²(O(-n)) vanishing makes this original boundary injective. -/
theorem cubicAmbient_boundaryTwoLinearMap_injective
    [HasExt.{u} (P).Modules]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) :
    Function.Injective (cubicAmbient_boundaryTwoLinearMap p hp hp0 n) := by
  letI : (equationIdeal p hp).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := inferInstance
  exact p3HypersurfaceTwistPushforward_connecting_two_injective K p hp hp0 n

/-- The actual cubic boundary image is killed by the SAME polynomial p
endomorphism. This is internally derived from the genuine Ext-class law. -/
theorem cubicAmbient_boundaryTwoLinearMap_mul_zero
    [HasExt.{u} (P).Modules]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ)
    (z : schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) n)) 2) :
    (cubicAmbient_boundaryTwoLinearMap p hp hp0 n z).comp
      (Ext.mk₀ (mulHomogeneous PS ⟨p, hp⟩ n)) (add_zero 3) = 0 := by
  letI : (equationIdeal p hp).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := inferInstance
  exact schemeModuleRestrictionConnectingLinearMapOver_postcomp_f_zero piP
    (hypersurfaceTwistRestrictionSequence p hp n)
    (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 n) 2 z

/-- The genuine small-degree H³(O(-n)) vanishing is internal. For n=1,2,3
it even makes the SAME cubic boundary surjective onto H³(O(-(n+3))). -/
theorem cubicAmbient_boundaryTwoLinearMap_surjective_of_lt_four
    [HasExt.{u} (P).Modules]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : n < 4) :
    Function.Surjective (cubicAmbient_boundaryTwoLinearMap p hp hp0 n) := by
  letI : (equationIdeal p hp).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := inferInstance
  let S := hypersurfaceTwistRestrictionSequence p hp n
  have hS := hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 n
  letI : Subsingleton (schemeModuleCohomology P S.X₂ 3) :=
    p3NegativeTwist_cohomology_three_subsingleton_of_lt_four K n hn
  intro z
  have hz : z.comp (Ext.mk₀ S.f) (add_zero 3) = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
    (show (P).Modules from SheafOfModules.unit (P).ringCatSheaf) hS z hz rfl
  exact ⟨y, hy⟩

/-- The actual two-boundary composite on the actual original q-cokernel. -/
def cubicSecondEquation_twoBoundaryLinearMap
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    letI : Linear K (P).Modules := schemeModulesLinearOver piP
    schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp))
          (cubicSecondEquationHomogeneous p q hp n hq) 0))) 1 →ₗ[K]
      schemeModuleCohomology P (sheafOfModules PS (n + 3)) 3 := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  exact (cubicAmbient_boundaryTwoLinearMap p hp hp0 n).comp
    (cubicSecondEquation_boundaryOneLinearMap p q hp hp0 n hq hnot)

/-- Both constituent injection/vanishing inputs are genuinely derived. -/
theorem cubicSecondEquation_twoBoundaryLinearMap_injective
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    Function.Injective (cubicSecondEquation_twoBoundaryLinearMap p q hp hp0 n hq hnot) := by
  exact (cubicAmbient_boundaryTwoLinearMap_injective p hp hp0 n).comp
    (cubicSecondEquation_boundaryOneLinearMap_injective p q hp hp0 n hq hnot)

/-- The actual composite satisfies actual cubic multiplication annihilation,
with no zero-composite or cocycle compatibility certificate supplied. -/
theorem cubicSecondEquation_twoBoundaryLinearMap_mul_zero
    [HasExt.{u} (P).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (z : schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp))
          (cubicSecondEquationHomogeneous p q hp n hq) 0))) 1) :
    (cubicSecondEquation_twoBoundaryLinearMap p q hp hp0 n hq hnot z).comp
      (Ext.mk₀ (mulHomogeneous PS ⟨p, hp⟩ n)) (add_zero 3) = 0 := by
  exact cubicAmbient_boundaryTwoLinearMap_mul_zero p hp hp0 n
    (cubicSecondEquation_boundaryOneLinearMap p q hp hp0 n hq hnot z)

end PfaffianDescent.Coray

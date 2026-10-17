import PfaffianDescent.CubicPointTraceFieldBaseChangeExtendedSupport
import PfaffianDescent.SchemeIsoClosedPointSupportTransport223
import PfaffianDescent.CubicPointTraceFieldBaseChangeNegativeTwist

/-! Actual diagonal support and original negative twist on the literal
coefficient-extended cubic. Neither comparison is an input. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  (i : Spec (.of L) ⟶ hypersurface p hp)
  (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The same diagonal point on the original coefficient-extended cubic. -/
def cubicDiagonalCoefficientPoint223 :
    Spec (.of L) ⟶ hypersurface (p.map (algebraMap K L)) (hp.map (algebraMap K L)) :=
  cubicPointTraceFieldBaseChangeRationalPoint K L (hypersurfaceToBase p hp) i hi ≫
    (hypersurfaceBaseChangeIso (algebraMap K L) p hp).inv

/-- The original closed point remains a literal closed immersion after
transport through the genuine hypersurface base-change isomorphism. -/
theorem cubicDiagonalCoefficientPoint_isClosedImmersion223 [IsClosedImmersion i] :
    IsClosedImmersion (cubicDiagonalCoefficientPoint223 K L p hp i hi) := by
  dsimp only [cubicDiagonalCoefficientPoint223]
  infer_instance

/-- Genuine base-change geometry proves rationality over the new field. -/
theorem cubicDiagonalCoefficientPoint_rational223 :
    cubicDiagonalCoefficientPoint223 K L p hp i hi ≫
      hypersurfaceToBase (p.map (algebraMap K L)) (hp.map (algebraMap K L)) =
        𝟙 (Spec (.of L)) := by
  rw [cubicDiagonalCoefficientPoint223, Category.assoc,
    ← hypersurfaceBaseChangeIso_hom_snd (algebraMap K L) p hp,
    Iso.inv_hom_id_assoc]
  exact cubicPointTraceFieldBaseChangeRationalPoint_snd K L (hypersurfaceToBase p hp) i hi

/-- Literal iterated pullback of the original negative twist identifies with
the native twist on the SAME coefficient-extended cubic. -/
def cubicDiagonalCoefficientNegativeTwistIso223 (m : ℕ) :
    (Scheme.Modules.pullback (hypersurfaceBaseChangeIso (algebraMap K L) p hp).hom).obj
      ((Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeProjection K L
        (hypersurfaceToBase p hp))).obj
          (sheafOfModules (grading (equationIdeal p hp)) m)) ≅
      sheafOfModules (grading (equationIdeal (p.map (algebraMap K L))
        (hp.map (algebraMap K L)))) m :=
  (Scheme.Modules.pullbackComp (hypersurfaceBaseChangeIso (algebraMap K L) p hp).hom
      (cubicPointTraceFieldBaseChangeProjection K L (hypersurfaceToBase p hp))).app _ ≪≫
    (Scheme.Modules.pullbackCongr
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap_eq_projection (algebraMap K L) p hp)).app _ ≪≫
    cubicPointTraceFieldBaseChangeCubicNegativeTwistIso (algebraMap K L) p hp m

end PfaffianDescent.ProjectiveNegativeTwist

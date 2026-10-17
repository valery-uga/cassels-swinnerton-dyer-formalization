import PfaffianDescent.AffineClosedImmersionIdealKernel
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelChartIdeal

/-! # Actual affine quotient ideal equals its literal normalized equation ideal -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceSpecMap_kernel_ideal
    (A B : CommRingCat.{u}) (φ : A ⟶ B) :
    (Spec.map φ).ker = Scheme.IdealSheafData.ofIdealTop
      ((RingHom.ker φ.hom).map (Scheme.ΓSpecIso A).inv.hom) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [specMap_ker_ideal_top, Scheme.IdealSheafData.ofIdealTop_ideal]
  change (RingHom.ker φ.hom).comap (Scheme.ΓSpecIso A).hom.hom =
    ((RingHom.ker φ.hom).map (Scheme.ΓSpecIso A).inv.hom).map
      ((Spec A).presheaf.map (𝟙 _)).hom
  rw [(Spec A).presheaf.map_id, CommRingCat.hom_id, Ideal.map_id]
  exact (Ideal.map_symm (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv).symm

theorem serreIncidenceSpecMap_kernel_span
    (A B : CommRingCat.{u}) (φ : A ⟶ B) {ι : Type*} (f : ι → A)
    (hf : RingHom.ker φ.hom = Ideal.span (Set.range f)) :
    (Spec.map φ).ker = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span (Set.range fun i => (Scheme.ΓSpecIso A).inv (f i))) := by
  refine (serreIncidenceSpecMap_kernel_ideal A B φ).trans ?_
  apply congrArg Scheme.IdealSheafData.ofIdealTop
  exact (congrArg (fun I => I.map (Scheme.ΓSpecIso A).inv.hom) hf).trans (by
    rw [Ideal.map_span, ← Set.range_comp])

theorem serreEvaluationKernel_projective_chart_equations
    {R : Type u} [CommRing R] (A : Matrix (Fin 6) (Fin 9) R) (j : Fin 9) :
    let I : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R) := ⊥
    (schemeQuotientMap I (serreEvaluationHomogeneousIdeal A) bot_le).ker.comap
      (chartι I j) = Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range fun r : Fin 6 =>
          (Scheme.ΓSpecIso (.of (ChartRing I j))).inv
            (∑ k : Fin 9, chartBaseMap I j (A r k) * chartCoordinate I j k))) := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R) := ⊥
  let J := serreEvaluationHomogeneousIdeal A
  let φ := CommRingCat.ofHom (chartQuotientMap I J bot_le j)
  let f : Fin 6 → ChartRing I j := fun r =>
    ∑ k : Fin 9, chartBaseMap I j (A r k) * chartCoordinate I j k
  have hf : RingHom.ker φ.hom = Ideal.span (Set.range f) :=
    serreEvaluationKernel_chart_ker A j
  exact (serreEvaluationKernel_projective_chart_ideal A j).trans
    (serreIncidenceSpecMap_kernel_span (.of (ChartRing I j)) (.of (ChartRing J j)) φ f hf)

end PfaffianDescent

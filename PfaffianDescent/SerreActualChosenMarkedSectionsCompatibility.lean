import PfaffianDescent.SerreActualChosenMarkedSections
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoefficientMarkedSupportAvoidance
import PfaffianDescent.SerreActualChosenMarkedResidualGeometryOfSection

/-! Compatibility of one typed chosen-section record with its actual field
base and original configuration point. These lemmas keep the zero family and
section record abstract, so their proofs do not reduce a pulled Serre module. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreActualChosenMarkedSections_marked_toFieldBase
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {X P Q Z : Scheme.{u}}
    (x : X ⟶ Spec (.of F)) (pp : P ⟶ Spec (.of F))
    (qp : Q ⟶ Spec (.of F)) (zero : Z ⟶ pullback x pp)
    [IsClosedImmersion zero]
    (q : Spec (.of F) ⟶ Q) (hq : q ≫ qp = 𝟙 _)
    (v : Q ⟶ P) (hv : v ≫ pp = qp)
    (d : SerreActualChosenMarkedSections x pp zero
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v))
    (n : Fin 3) :
    serreActualChosenFibre_marked x pp zero
        ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) d.δ n ≫ x =
      Spec.map (CommRingCat.ofHom (algebraMap F E)) := by
  rw [serreActualChosenFibre_marked_toBase x pp zero _ d.δ d.hδ n]
  rw [Category.assoc, Category.assoc, hv, hq, Category.comp_id]

theorem serreActualChosenMarkedSections_surface_original_of_configuration
    {F E : Type u} [Field F] [Field E]
    {X P Z Y B I : Scheme.{u}}
    (x : X ⟶ Spec (.of F)) (pp : P ⟶ Spec (.of F))
    (zero : Z ⟶ pullback x pp) (t : Spec (.of E) ⟶ P)
    (d : SerreActualChosenMarkedSections x pp zero t)
    (f : X ⟶ Y) (π : I ⟶ B) (s : Spec (.of E) ⟶ I)
    (c : Spec (.of E) ⟶ B) (marked : B ⟶ Y) (n : Fin 3)
    (hSurface : serreActualChosenFibre_marked x pp zero t d.δ n ≫ f =
      s ≫ π ≫ marked) (hcfg : s ≫ π = c) :
    serreActualChosenFibre_marked x pp zero t d.δ n ≫ f = c ≫ marked := by
  exact hSurface.trans (by rw [← Category.assoc, hcfg])

theorem serreActualChosenMarkedSections_coefficientMarked_not_mem_range
    {K F E : Type u} [Field K] [Field F] [Field E]
    (g : K →+* F) (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {D P Z : Scheme.{u}} [IsAffine D]
    (i : D ⟶ hypersurface p hp) [IsClosedImmersion i]
    (pp : P ⟶ Spec (.of F))
    (zero : Z ⟶ pullback
      (hypersurfaceToBase (p.map g) (hp.map g)) pp)
    (t : Spec (.of E) ⟶ P)
    (d : SerreActualChosenMarkedSections
      (hypersurfaceToBase (p.map g) (hp.map g)) pp zero t)
    (n : Fin 3) (original : Spec (.of E) ⟶ hypersurface p hp)
    (hOriginal : serreActualChosenFibre_marked
      (hypersurfaceToBase (p.map g) (hp.map g)) pp zero t d.δ n ≫
        cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp = original)
    (hout : original (IsLocalRing.closedPoint E) ∉ Set.range i) :
    (serreActualChosenFibre_marked
      (hypersurfaceToBase (p.map g) (hp.map g)) pp zero t d.δ n)
        (IsLocalRing.closedPoint E) ∉ Set.range
      (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint g p hp i) :=
  cubicClosedPointSerreFiniteZeroResidual_coefficientMarked_not_mem_range
    g p hp i _ original hOriginal (IsLocalRing.closedPoint E) hout

def serreActualChosenMarkedResidualGeometry_of_sections
    {F E L : Type u} [Field F] [Field E] [Field L] [Algebra F E]
    {X P Q Z I : Scheme.{u}}
    (x : X ⟶ Spec (.of F)) (pp : P ⟶ Spec (.of F))
    (qp : Q ⟶ Spec (.of F)) (zero : Z ⟶ pullback x pp)
    (i : I ⟶ X) (j : Spec (.of L) ⟶ X)
    (q : Spec (.of F) ⟶ Q) (hq : q ≫ qp = 𝟙 _)
    (v : Q ⟶ P) (hv : v ≫ pp = qp)
    (d : SerreActualChosenMarkedSections x pp zero
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v))
    (n : Fin 3)
    (hf : IsField ((pullback (zero ≫ pullback.snd x pp)
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v)).presheaf.stalk
        ((d.δ n) (IsLocalRing.closedPoint E))))
    (hout : (serreActualChosenFibre_marked x pp zero
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) d.δ n)
        (IsLocalRing.closedPoint E) ∉ Set.range i)
    (hpoint : (serreActualChosenFibre_marked x pp zero
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) d.δ n)
        (IsLocalRing.closedPoint E) = j (IsLocalRing.closedPoint L)) :
    SerreActualChosenMarkedResidualGeometry x pp zero i j
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) :=
  serreActualChosenMarkedResidualGeometry_of_section
    x pp qp zero i j q hq v hv d.δ d.hδ n hf hout hpoint

end PfaffianDescent

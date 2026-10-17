import PfaffianDescent.NativeWholeOpenPointCuts317
import PfaffianDescent.OriginalNormalizedProjectiveReduction312

/-! SOURCE ONLY317. Actual chart conversion isolated from the Artinian lift
provider. All separated/open dictionaries come from explicit existing proofs. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma originalNormalizedWholeOpen_separated317
    {B : Type u} [CommRing B] (r : MvPolynomial (Fin 4) B)
    {d : ℕ} (hr : r.IsHomogeneous d) : IsSeparated (hypersurfaceToBase r hr) :=
  @IsProper.toIsSeparated _ _ _ (isProper_hypersurfaceToBase r hr)

local instance normalizedWholeOpenActualChartOpen317
    {B : Type u} [CommRing B] (r : MvPolynomial (Fin 4) B)
    {d : ℕ} (hr : r.IsHomogeneous d) (j : Fin 4) :
    IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 r hr j) :=
  originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 r hr j

variable {B : Type u} [CommRing B] (r : MvPolynomial (Fin 4) B)
variable {d : ℕ} (hr : r.IsHomogeneous d) (j : Fin 4) (n : ℕ)
variable (I : FiniteFlatHilbertPoint195 (hypersurfaceToBase r hr) n)
variable (QU : FiniteFlatHilbertPoint195
  ((originalNormalizedHypersurfaceChartEmbedding312 r hr j).opensRange.ι ≫
    hypersurfaceToBase r hr) n)
variable (hwhole : QU.val.map
  (originalNormalizedHypersurfaceChartEmbedding312 r hr j).opensRange.ι = I.val)

/-- Conversion of an ACTUAL normalized original whole open point, with no
Artinian or residue assumptions in this bounded construction. -/
def originalNormalizedWholeOpen_chartPoint317 : FiniteFlatHilbertPoint195
    (Spec.map (CommRingCat.ofHom (R := B)
      (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
      (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j)))) n := by
  letI : IsSeparated (hypersurfaceToBase r hr) :=
    originalNormalizedWholeOpen_separated317 r hr
  exact nativeWholePointPushedOpen_chartPoint317
    (Y := Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 r j)))
    (X := hypersurface r hr) (T := Spec (.of B))
    (hypersurfaceToBase r hr) n
    (originalNormalizedHypersurfaceChartEmbedding312 r hr j)
    (Spec.map (CommRingCat.ofHom (R := B)
      (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
      (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
    (originalNormalizedHypersurfaceChartEmbedding_toBase312 r hr j) I QU hwhole

lemma originalNormalizedWholeOpen_chartPoint_wholeIdeal317 :
    (originalNormalizedWholeOpen_chartPoint317 r hr j n I QU hwhole).val =
      I.val.comap (originalNormalizedHypersurfaceChartEmbedding312 r hr j) := by
  letI : IsSeparated (hypersurfaceToBase r hr) :=
    originalNormalizedWholeOpen_separated317 r hr
  exact nativeWholePointPushedOpen_chartPoint_wholeIdeal317
    (Y := Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 r j)))
    (X := hypersurface r hr) (T := Spec (.of B))
    (hypersurfaceToBase r hr) n
    (originalNormalizedHypersurfaceChartEmbedding312 r hr j)
    (Spec.map (CommRingCat.ofHom (R := B)
      (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
      (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
    (originalNormalizedHypersurfaceChartEmbedding_toBase312 r hr j) I QU hwhole

end PfaffianDescent
end

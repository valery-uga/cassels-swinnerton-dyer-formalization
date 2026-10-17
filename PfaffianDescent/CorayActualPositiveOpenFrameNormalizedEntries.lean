import PfaffianDescent.CorayActualPositiveWeightedNativeChartEntries

/-! Actual normalized matrix coefficients on EVERY subopen of the original
coordinate chart. The formula is derived from the actual positive inverse
frame and actual homogeneous multiplication, not supplied as a comparison.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Opposite
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The literal normalized coefficient, as an actual regular function on
an actual subopen of the ambient coordinate chart. -/
def actualAmbientChartCoefficientSection (j : Fin 4)
    (U : (Proj PS).Opens) (hU : U ≤ p3StandardOpen (K := K) j) (p : A) :
    Γ(Proj PS, U) :=
  (Proj PS).presheaf.map (homOfLE hU).op
    (Proj.awayToSection PS (X j) (ambientChartEvaluation j p))

/-- Its value is the original native degree-zero localization map, with no
transported scalar action or chosen map to the point's residue field. -/
theorem actualAmbientChartCoefficientSection_apply
    (j : Fin 4) (U : (Proj PS).Opens)
    (hU : U ≤ p3StandardOpen (K := K) j) (p : A) (x : U) :
    letI : (positivePointIdeal PS x.1).IsPrime := ProjectiveSpectrum.isPrime x.1
    (actualAmbientChartCoefficientSection j U hU p).1 x =
      HomogeneousLocalization.mapId PS
        (Submonoid.powers_le.mpr (show X j ∈ (positivePointIdeal PS x.1).primeCompl
          from hU x.2)) (ambientChartEvaluation j p) := by
  letI : (positivePointIdeal PS x.1).IsPrime := ProjectiveSpectrum.isPrime x.1
  rfl

private lemma positiveStructureFrame_inv_val
    (U : (Proj PS).Opens) (j : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) j) (m : ℕ)
    (r : Γ(Proj PS, U)) (x : U) :
    ((p3PositiveTwistSectionsIsoStructure K U j hU m).inv r).1 x =
      algebraMap A (PositiveFiber PS x.1) ((X j) ^ m) * (r.1 x).val := by
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let q : Γ((U : Scheme), ⊤) := F.map U.topIso.inv r
  have htop : F.map U.topIso.hom q = r :=
    ConcreteCategory.congr_hom (F.mapIso U.topIso).inv_hom_id r
  have hv := p3PositiveTwistSectionsIsoUnit_inv_apply_val K U j hU m q x
  change ((p3PositiveTwistSectionsIsoUnit K U j hU m).inv q).1 x = _
  calc
    _ = algebraMap A (PositiveFiber PS x.1) ((X j) ^ m) *
        ((F.map U.topIso.hom q).1 x).val := hv
    _ = _ := congrArg (fun t : Γ(Proj PS, U) =>
      algebraMap A (PositiveFiber PS x.1) ((X j) ^ m) * (t.1 x).val) htop

private lemma normalizedCoefficient_positiveGenerator_product
    (j : Fin 4) {d : ℕ} (p : A) (hp : p.IsHomogeneous d)
    (a : ℕ) (x : ProjectiveSpectrum.top PS)
    (hj : X j ∈ (positivePointIdeal PS x).primeCompl) :
    letI : (positivePointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x
    algebraMap A (PositiveFiber PS x) p *
        algebraMap A (PositiveFiber PS x) ((X j) ^ a) =
      (HomogeneousLocalization.mapId PS (Submonoid.powers_le.mpr hj)
          (ambientChartEvaluation j p)).val *
        algebraMap A (PositiveFiber PS x) ((X j) ^ (a + d)) := by
  letI : (positivePointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x
  let P := positivePointIdeal PS x
  let s : PS d := ⟨p, hp⟩
  let f : PS 1 := ⟨X j, isHomogeneous_X K j⟩
  have ht := congrArg Subtype.val
    (positiveMulHomogeneousStalk_localGenerator PS P s f hj a)
  change algebraMap A (PositiveFiber PS x) p *
      algebraMap A (PositiveFiber PS x) ((X j) ^ a) =
    (localEquation PS P s f hj).val *
      algebraMap A (PositiveFiber PS x) ((X j) ^ (a + d)) at ht
  have hc := actualAmbientChartCoefficient_atPrime j p hp P hj
  exact ht.trans (congrArg (fun c : HomogeneousLocalization.AtPrime PS P =>
    c.val * algebraMap A (PositiveFiber PS x) ((X j) ^ (a + d))) hc.symm)

/-- Actual homogeneous multiplication in the ACTUAL positive chart frame
is multiplication by the literal normalized chart coefficient on EVERY
subopen. This supplies the matrix-entry comparison without a comparison
premise, even for arbitrary homogeneous ideals with nilpotents. -/
theorem actualPositiveWeightedMultiplication_structureFrame
    (j : Fin 4) {d : ℕ} (p : A) (hp : p.IsHomogeneous d)
    (a b : ℕ) (h : a + d = b) (U : (Proj PS).Opens)
    (hU : U ≤ p3StandardOpen (K := K) j) (r : Γ(Proj PS, U)) :
    (actualPositiveWeightedMultiplication p hp a b h).val.app (op U)
        ((p3PositiveTwistSectionsIsoStructure K U j hU a).inv r) =
      (p3PositiveTwistSectionsIsoStructure K U j hU b).inv
        (actualAmbientChartCoefficientSection j U hU p * r) := by
  cases h
  apply Subtype.ext
  funext x
  change U at x
  letI : (positivePointIdeal PS x.1).IsPrime := ProjectiveSpectrum.isPrime x.1
  let s : (positiveSheafOfModules PS a).val.obj (op U) :=
    (p3PositiveTwistSectionsIsoStructure K U j hU a).inv r
  let t : Γ(Proj PS, U) := actualAmbientChartCoefficientSection j U hU p * r
  have hmul := actualPositiveWeightedMultiplication_apply_val p hp a (a + d) rfl U s x
  have ha := positiveStructureFrame_inv_val U j hU a r x
  have hb := positiveStructureFrame_inv_val U j hU (a + d) t x
  have hleft : ((actualPositiveWeightedMultiplication p hp a (a + d) rfl).val.app (op U) s).1 x =
      algebraMap A (PositiveFiber PS x.1) p *
        (algebraMap A (PositiveFiber PS x.1) ((X j) ^ a) * (r.1 x).val) :=
    hmul.trans (congrArg (fun z : PositiveFiber PS x.1 =>
      algebraMap A (PositiveFiber PS x.1) p * z) ha)
  let hj : X j ∈ (positivePointIdeal PS x.1).primeCompl := hU x.2
  have hc := normalizedCoefficient_positiveGenerator_product j p hp a x.1 hj
  have he := actualAmbientChartCoefficientSection_apply j U hU p x
  have hev : ((actualAmbientChartCoefficientSection j U hU p).1 x).val =
      (HomogeneousLocalization.mapId PS (Submonoid.powers_le.mpr hj)
        (ambientChartEvaluation j p)).val := congrArg (fun z : HomogeneousLocalization.AtPrime PS
        (positivePointIdeal PS x.1) => z.val) he
  have hprod : algebraMap A (PositiveFiber PS x.1) p *
      (algebraMap A (PositiveFiber PS x.1) ((X j) ^ a) * (r.1 x).val) =
    algebraMap A (PositiveFiber PS x.1) ((X j) ^ (a + d)) * (t.1 x).val := by
    change algebraMap A (PositiveFiber PS x.1) p *
        (algebraMap A (PositiveFiber PS x.1) ((X j) ^ a) * (r.1 x).val) =
      algebraMap A (PositiveFiber PS x.1) ((X j) ^ (a + d)) *
        ((actualAmbientChartCoefficientSection j U hU p).1 x * r.1 x).val
    calc
      _ = (algebraMap A (PositiveFiber PS x.1) p *
          algebraMap A (PositiveFiber PS x.1) ((X j) ^ a)) * (r.1 x).val :=
        (mul_assoc _ _ _).symm
      _ = ((HomogeneousLocalization.mapId PS (Submonoid.powers_le.mpr hj)
          (ambientChartEvaluation j p)).val *
          algebraMap A (PositiveFiber PS x.1) ((X j) ^ (a + d))) * (r.1 x).val :=
        congrArg (fun c => c * (r.1 x).val) hc
      _ = _ := by
        rw [HomogeneousLocalization.val_mul, hev]
        ring
  exact hleft.trans (hprod.trans hb.symm)

end PfaffianDescent.Coray

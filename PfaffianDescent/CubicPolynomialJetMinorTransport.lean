import PfaffianDescent.CubicPolynomialTangentFrames

/-! Coefficient and determinant-open transport of native polynomial jets. -/

noncomputable section
namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.UniversalHomogeneous

universe u v
set_option backward.isDefEq.respectTransparency false

def cubicPolynomialSurfaceTangentRows
    {R : Type u} [CommRing R]
    (p : MvPolynomial (Fin 4) R) (x : Fin 11 → Fin 4 → R)
    (anchor : Fin 3 → Fin 4) (pivot : Fin 3 → Fin 3) : Fin 3 → Fin 4 → Fin 2 → R :=
  fun i => cubicPolynomialTangentRow (anchor i)
    (fun j => (pderiv j p).eval (x (i.castAdd 8))) (pivot i)

theorem cubicPolynomialSurfaceTangentRows_map
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (f : R →+* S) (p : MvPolynomial (Fin 4) R) (x : Fin 11 → Fin 4 → R)
    (anchor : Fin 3 → Fin 4) (pivot : Fin 3 → Fin 3) :
    (fun i j t => f (cubicPolynomialSurfaceTangentRows p x anchor pivot i j t)) =
      cubicPolynomialSurfaceTangentRows (p.map f) (fun i j => f (x i j)) anchor pivot := by
  funext i
  rw [show (fun j t => f (cubicPolynomialSurfaceTangentRows p x anchor pivot i j t)) =
    (fun j t => f (cubicPolynomialTangentRow (anchor i)
      (fun k => (pderiv k p).eval (x (i.castAdd 8))) (pivot i) j t)) by rfl,
    cubicPolynomialTangentRow_map]
  congr 1
  funext j
  rw [MvPolynomial.map_eval, ← MvPolynomial.pderiv_map]
  rfl

/-- The specialized polynomial jets lie on the actual cubic equation;
their gradient relation is constructed, rather than supplied. -/
theorem cubicPolynomialSurfaceTangentRows_firstJets_cubic
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (x : Fin 11 → Fin 4 → K)
    (anchor : Fin 3 → Fin 4) (pivot : Fin 3 → Fin 3)
    (hpx : ∀ i : Fin 3, aeval (x (i.castAdd 8)) p = 0) :
    ∀ i, aeval (cubicFullJetCoordinates x
      (cubicPolynomialSurfaceTangentRows p x anchor pivot) i) p = 0 := by
  intro i
  unfold cubicFullJetCoordinates
  rw [cubicClosedPointSerreSurfaceJets_taylor, hpx i]
  have hg := cubicPolynomialTangentRow_gradient_zero (anchor i)
    (fun j => aeval (x (i.castAdd 8)) (pderiv j p)) (pivot i)
  have hrows : cubicPolynomialSurfaceTangentRows p x anchor pivot i =
      cubicPolynomialTangentRow (anchor i)
        (fun j => aeval (x (i.castAdd 8)) (pderiv j p)) (pivot i) := by
    simp only [cubicPolynomialSurfaceTangentRows, aeval_eq_eval]
  rw [hrows, hg]
  simp

@[simp] theorem cubicPolynomialSurfaceTangentRows_firstJets_anchor
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (x : Fin 11 → Fin 4 → K)
    (anchor : Fin 3 → Fin 4) (pivot : Fin 3 → Fin 3)
    (hx : ∀ i : Fin 3, x (i.castAdd 8) (anchor i) = 1) (i : Fin 3) :
    cubicFullJetCoordinates x (cubicPolynomialSurfaceTangentRows p x anchor pivot) i
      (anchor i) = 1 := by
  simp [cubicFullJetCoordinates, cubicPolynomialSurfaceTangentRows, hx]

def cubicPolynomialJetMinorDet
    {R : Type u} [CommRing R]
    (p : MvPolynomial (Fin 4) R) (x : Fin 11 → Fin 4 → R)
    (anchor : Fin 3 → Fin 4) (pivot : Fin 3 → Fin 3)
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3) : R :=
  homogeneousFullJetMinorDet m x (cubicPolynomialSurfaceTangentRows p x anchor pivot)

theorem cubicPolynomialJetMinorDet_map
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (f : R →+* S) (p : MvPolynomial (Fin 4) R) (x : Fin 11 → Fin 4 → R)
    (anchor : Fin 3 → Fin 4) (pivot : Fin 3 → Fin 3)
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3) :
    f (cubicPolynomialJetMinorDet p x anchor pivot m) =
      cubicPolynomialJetMinorDet (p.map f) (fun i j => f (x i j)) anchor pivot m := by
  unfold cubicPolynomialJetMinorDet homogeneousFullJetMinorDet
  rw [RingHom.map_det, RingHom.mapMatrix_apply, homogeneousFullJetEvaluationMinor_map,
    cubicPolynomialSurfaceTangentRows_map]

/-- Every field point of the actual polynomial minor open has full cubic
interpolation in its own native specialized polynomial tangent frames. -/
theorem cubicPolynomialJetMinor_interpolation_on_principalOpen
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (p : MvPolynomial (Fin 4) R) (x : Fin 11 → Fin 4 → R)
    (anchor : Fin 3 → Fin 4) (pivot : Fin 3 → Fin 3)
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3)
    (g : Localization.Away (cubicPolynomialJetMinorDet p x anchor pivot m) →+* F) :
    let S := Localization.Away (cubicPolynomialJetMinorDet p x anchor pivot m)
    let f : R →+* F := g.comp (algebraMap R S)
    let xF : Fin 11 → Fin 4 → F := fun i j => f (x i j)
    Function.Surjective (cubicElevenPointFullJetRestriction xF
      (cubicFullJetCoordinates xF
        (cubicPolynomialSurfaceTangentRows (p.map f) xF anchor pivot))) := by
  let S := Localization.Away (cubicPolynomialJetMinorDet p x anchor pivot m)
  let f : R →+* F := g.comp (algebraMap R S)
  have h := cubicFullJetCoordinates_interpolation_on_minorOpen_fieldPoint x
    (cubicPolynomialSurfaceTangentRows p x anchor pivot) m g
  change Function.Surjective (cubicElevenPointFullJetRestriction
    (fun i j => f (x i j)) (cubicFullJetCoordinates (fun i j => f (x i j))
      (fun i j t => f (cubicPolynomialSurfaceTangentRows p x anchor pivot i j t)))) at h
  rw [cubicPolynomialSurfaceTangentRows_map] at h
  exact h

end PfaffianDescent

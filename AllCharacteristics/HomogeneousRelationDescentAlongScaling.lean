import AllCharacteristics.HomogeneousSpecialization
import Mathlib.RingTheory.Ideal.Maps

/-!
# Retaining homogeneous relation detection through scalar descent

The descended vector and the raw secant vector differ by one nonzero scalar
after coefficient extension.  Any homogeneous relation of the descended
vector therefore yields a homogeneous relation of the raw vector.  This also
works after embedding the raw polynomial ring in its fraction field.
-/

namespace AllCharacteristics

universe u

/-- Homogeneous relation detection descends through a coefficient map when
the actual coordinate vectors agree up to a nonzero scalar. -/
theorem homogeneous_relation_of_mapped_scaled_vector
    {k S T : Type u} [CommRing k] [CommRing S] [CommRing T] [IsDomain T]
    {σ : Type}
    (μ : S →+* T) (κS : k →+* S) (κT : k →+* T)
    (hbase : μ.comp κS = κT)
    (R : σ → S) (r : σ → T) (t : T) (ht : t ≠ 0)
    (hR : (fun i => μ (R i)) = t • r)
    (I : Ideal (MvPolynomial σ k))
    (hdetect : ∀ (p : MvPolynomial σ k) (e : ℕ),
      p.IsHomogeneous e → p.eval₂ κT r = 0 → p ∈ I)
    (G : MvPolynomial σ k) (d : ℕ) (hG : G.IsHomogeneous d)
    (hzero : G.eval₂ κS R = 0) : G ∈ I := by
  have hscaled : G.eval₂ κT (t • r) = 0 := by
    rw [← hR, ← hbase, ← MvPolynomial.hom_eval₂, hzero, map_zero]
  rw [eval₂_homogeneous_smul G hG] at hscaled
  apply hdetect G d hG
  exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero d ht)

/-- The exact scalar relation from polynomial descent can be compared with
the raw vector after any injective embedding, in particular in the raw
polynomial ring's fraction field. -/
theorem homogeneous_relation_of_descent_scaling_after_embedding
    {k S B T : Type u} [CommRing k] [CommRing S] [CommRing B]
    [CommRing T] [IsDomain T] {σ : Type}
    (μ : S →+* B) (ι : B →+* T) (hι : Function.Injective ι)
    (κS : k →+* S) (κT : k →+* T)
    (hbase : (ι.comp μ).comp κS = κT)
    (R : σ → S) (r : σ → B) (s : B) (hs : s ≠ 0)
    (hR : ∀ i, μ (R i) = s * r i)
    (I : Ideal (MvPolynomial σ k))
    (hdetect : ∀ (p : MvPolynomial σ k) (e : ℕ), p.IsHomogeneous e →
      p.eval₂ κT (fun i => ι (r i)) = 0 → p ∈ I)
    (G : MvPolynomial σ k) (d : ℕ) (hG : G.IsHomogeneous d)
    (hzero : G.eval₂ κS R = 0) : G ∈ I := by
  have hs' : ι s ≠ 0 := fun hz => hs (hι (hz.trans (map_zero ι).symm))
  have hR' : (fun i => (ι.comp μ) (R i)) = ι s • (fun i => ι (r i)) := by
    funext i
    change ι (μ (R i)) = ι s * ι (r i)
    rw [hR i, map_mul]
  exact homogeneous_relation_of_mapped_scaled_vector
    (ι.comp μ) κS κT hbase R (fun i => ι (r i)) (ι s) hs' hR'
    I hdetect G d hG hzero

end AllCharacteristics

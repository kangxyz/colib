# Auxiliary-support forgetting

COL-0336 adapts Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
SupportedOpen/Forget.lean:30-92 and GlobalLocalization.lean:172-207.

PerfectSupportedOpenForget uses the actual perfectSupportedInclusion for coarse
support forgetting. The literal union-support inclusion retains j-relative acyclicity.
Its flattening square instantiates the generic changeWeakConnectingHom_natural on
these exact functors, retaining the original boundary and sign in every degree.
The union-to-base and existing fine restriction-forget squares complete the fixed-pair
map of long exact sequences.

SupportedOpenFineForget transports through the actual positive restriction equivalences.
The ordinary inverse is OpenDerivedImage.relativeKRestrictEquiv with the native qcqs
roofs and complements, not a newly selected equivalence. Both compact U and compact
union are present: union compactness alone does not supply the ordinary comparison.
The original compact-U/compact-T corollaries are retained. The boundary at n = 0
is K1 to K0; the positive inverse at n = 0 is a K1 inverse, not a K0 inverse.

These statements concern K-groups. All-stage preservation of the specified prespectrum
nullhomotopy is a separate remaining coherence obligation. Neither arbitrary global-pair
naturality nor Bass localization is included.

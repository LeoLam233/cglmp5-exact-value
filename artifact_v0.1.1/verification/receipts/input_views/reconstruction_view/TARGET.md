# Permitted reconstruction input: C001, target and definitions only

This is an AI-assisted candidate, not an assumed theorem. Derive what you can;
do not use a candidate-specific unproved lemma as authority. You have not been
given its proof, witness, SOS certificate, discovery scripts, or PASS summaries.

Alice and Bob each have two measurements A0,A1 and B0,B1 with outcomes 0..4.
All event equalities below are modulo 5. States are normalized bipartite quantum
states and measurements are arbitrary local five-outcome POVMs in arbitrary
Hilbert-space dimension. Define

I5 = sum_{k=0,1} (1-k/2) [
P(A0=B0+k)+P(B0=A1+k+1)+P(A1=B1+k)+P(B1=A0+k)
-P(A0=B0-k-1)-P(B0=A1-k)-P(A1=B1-k-1)-P(B1=A0-k-1)].

The candidate target is sup I5 = mu, where mu is the largest real root of
p(t)=5t^6-65t^4+144t^2+96t+16 (approximately 3.0157104755226733).
The supplied value is exposure, not independent discovery.

Admissible background: basic linear algebra, spectral theorem, elementary exact
polynomial arithmetic, Born rule, and finite-outcome Naimark dilation with its
hypotheses stated and checked. No solution-specific black box is supplied.

Complementary bounded task: independently construct and validate an attainable
lower bound, ideally reaching mu. Derive measurement phases/state instead of
consulting the candidate. Establish normalization and the exact characteristic
polynomial and eigenvector if feasible. Do not call the numerical lower bound a
universal upper proof. A partial or unsuccessful attempt is acceptable evidence.

Input boundary: read only this directory, ordinary mathematical reference
sources if necessary, and your newly generated files in the assigned output
directory. Do not inspect other workspace directories, memory, candidate or
audit files, user conversation, or other agents' results. No technical isolation
is promised; actual exposures must be reported. Freeze your unguided attempt
before requesting method-only guidance. Record computations, commands, versions,
input SHA-256, scope, blockers and limitations. Do not publish or message users.

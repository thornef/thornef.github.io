\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Sym2(3)--Ternary quadratic forms
\\\\\\\\\\\\\\\\\\\\\\\\\\\\

\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ orbit size;
\\\\\\\\\\\\\\\\\\\\\\\\\\\\
ors=[1, q^3 - 1, q*(q^3 - 1)*(q + 1)/2, q*(q^3 - 1)*(q - 1)/2, (q^5 - q^2)*(q - 1)];
zeroes = [q^2 + q + 1, q + 1, 2*q + 1, 1, q + 1];
ORS=matdiagonal(ors);

\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Counting elements in subspaces
\\\\\\\\\\\\\\\\\\\\\\\\\\\\

W0 = [1,0,0,0,0];
W1 = [1,q-1,0,0,0];
W2 = [1, 2*q - 2, (q - 1)^2/2, (q - 1)^2/2, 0];
W3 = [1, q^2 - 1, (q/2)*(3*q^2 - 2*q - 1), (q/2)*(q - 1)^2, q^2*(q - 1)^2];
W0P = ors;
W1P = vector(5, i, W0P[i] * zeroes[i]/(q^2 + q + 1));
W2P = vector(5, i, W1P[i] * (zeroes[i] - 1)/(q^2 + q));

M1 = matrix(5, 5);
M2 = matrix(5, 5);

for(i=1,5,M1[1,i]=W0[i]/ors[i]);
for(i=1,5,M1[2,i]=W1[i]/ors[i]);
for(i=1,5,M1[3,i]=W2[i]/ors[i]);
for(i=1,5,M1[4,i]=W1P[i]/ors[i]);
for(i=1,5,M1[5,i]=W0P[i]/ors[i]);

for(i=1,5,M2[1,i]=      W0P[i]/ors[i]);
for(i=1,5,M2[2,i]=q   * W1P[i]/ors[i]);
for(i=1,5,M2[3,i]=q^2 * W2P[i]/ors[i]);
for(i=1,5,M2[4,i]=q^5 * W1[i]/ors[i]);
for(i=1,5,M2[5,i]=q^6 * W0[i]/ors[i]);

M = (M1^-1 * M2)~;

\\ Note: this is really q^d times M

print(M);

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Check that M satisfy Lemma 6 \\
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

T=ORS*M;
TBZ=T-T~;

{
if(TBZ==matrix(5,5),
	print("  -- M is symmetric in the sense of Lemma 6"),
	print("  -- M is NOT symmetric in the sense of Lemma 6")
);
}

{
if(M*M==q^6*matid(5),
	print("  -- M^2 is the scalar matrix"),
	print("  -- M^2 is NOT the scalar matrix")
);
}

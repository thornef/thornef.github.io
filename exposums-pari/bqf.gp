\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Sym2(2)--Binary quadratic forms
\\\\\\\\\\\\\\\\\\\\\\\\\\\\

\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ orbit size;
\\\\\\\\\\\\\\\\\\\\\\\\\\\\
ors=[1, q^2 - 1, q*(q^2 - 1)/2, q*(q - 1)^2/2];
ORS=matdiagonal(ors);

\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Counting elements in subspaces
\\\\\\\\\\\\\\\\\\\\\\\\\\\\

W0=[1,0,0,0];
W1 = [1, q-1, 0, 0];
W2 = [1, q-1, q^2 - q, 0];
W3 = ors;

M1 = matrix(4, 4);
M2 = matrix(4, 4);

for(i=1,4,M1[1,i]=W0[i]/ors[i]);
for(i=1,4,M1[2,i]=W1[i]/ors[i]);
for(i=1,4,M1[3,i]=W2[i]/ors[i]);
for(i=1,4,M1[4,i]=W3[i]/ors[i]);

for(i=1,4,M2[1,i]=      W3[i]/ors[i]);
for(i=1,4,M2[2,i]=q   * W2[i]/ors[i]);
for(i=1,4,M2[3,i]=q^2 * W1[i]/ors[i]);
for(i=1,4,M2[4,i]=q^3 * W0[i]/ors[i]);

M = (M1^-1 * M2)~;

\\ Note: this is really q^3 times the M of Theorem 12

print(M);

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Check that M satisfy Lemma 6 \\
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

T=ORS*M;
TBZ=T-T~;

{
if(TBZ==matrix(4,4),
	print("  -- M is symmetric in the sense of Lemma 6"),
	print("  -- M is NOT symmetric in the sense of Lemma 6")
);
}

{
if(M*M==q^3*matid(4),
	print("  -- M^2 is the scalar matrix"),
	print("  -- M^2 is NOT the scalar matrix")
);
}



\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Compute some Fourier transforms
\\\\\\\\\\\\\\\\\\\\\\\\\\\\

sing=[1,1,0,0];
quad=[0,0,1,-1];

print("* Fourier transform of singular sets:");
print(sing*M~);
print("* Fourier transform of the quadratic character:");
print(quad*M~);

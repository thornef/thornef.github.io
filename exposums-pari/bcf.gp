\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Sym3(2)--Binary cubic forms
\\\\\\\\\\\\\\\\\\\\\\\\\\\\
 

q1 = q^2 - 1;
q2 = q^2 - q;

\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ orbit size;
\\\\\\\\\\\\\\\\\\\\\\\\\\\\
ors=[1, q1, q*q1, q1*q2/6, q1*q2/2, q1*q2/3];
ORS=matdiagonal(ors);

\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Counting elements in subspaces
\\\\\\\\\\\\\\\\\\\\\\\\\\\\

W0=[1,0,0,0,0,0];
W0P = ors;
W1=[1, q-1, 0,0,0,0];

mul = [1, 1/(q + 1), 2/(q + 1), 3/(q + 1), 1/(q + 1), 0];
W1P = vector(6, i, ors[i] * mul[i]);

W2 = [1, q-1, q*(q - 1), 0,0,0];
W3 = [1, 0, 2*(q - 1), (q - 1)^2, 0,0];
W3Pa = [1, 2*(q - 1), 0, (q - 1)^2/3, 0, 2*(q - 1)^2/3];
W3Pb = [1, 2*(q - 1), 0, 0, (q - 1)^2, 0];

W3P = W3Pb; \\ checked with both

M1 = matrix(6, 6);
M2 = matrix(6, 6);

for(i=1,6,M1[1,i]=W0[i]/ors[i]);
for(i=1,6,M1[2,i]=W1[i]/ors[i]);
for(i=1,6,M1[3,i]=W2[i]/ors[i]);
for(i=1,6,M1[4,i]=W3[i]/ors[i]);
for(i=1,6,M1[5,i]=W1P[i]/ors[i]);
for(i=1,6,M1[6,i]=W0P[i]/ors[i]);

for(i=1,6,M2[1,i]=      W0P[i]/ors[i]);
for(i=1,6,M2[2,i]=q   * W1P[i]/ors[i]);
for(i=1,6,M2[3,i]=q^2 * W2[i]/ors[i]);
for(i=1,6,M2[4,i]=q^2 * W3P[i]/ors[i]);
for(i=1,6,M2[5,i]=q^3 * W1[i]/ors[i]);
for(i=1,6,M2[6,i]=q^4 * W0[i]/ors[i]);

M = (M1^-1 * M2)~;

\\ Note: this is really q^4 times the M of Theorem 12
print(M);

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Check that M satisfy Lemma 6 \\
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

T=ORS*M;
TBZ=T-T~;

{
if(TBZ==matrix(6,6),
	print("  -- M is symmetric in the sense of Lemma 6"),
	print("  -- M is NOT symmetric in the sense of Lemma 6")
);
}

{
if(M*M==q^4*matid(6),
	print("  -- M^2 is the scalar matrix"),
	print("  -- M^2 is NOT the scalar matrix")
);
}



\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Compute some Fourier transforms
\\\\\\\\\\\\\\\\\\\\\\\\\\\\

sing=[1,1,1,0,0,0];
quad=[0,0,0,1,-1,1];

print("* Fourier transform of singular sets:");
print(sing*M~);
print("* Fourier transform of the quadratic charcter:");
print(quad*M~);

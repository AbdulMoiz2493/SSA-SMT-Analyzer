
export const examplePrograms = {
  verification: [
    {
      name: "If-Else Example",
      code: `x := 3;
if (x < 5) {
  y := x + 1;
} else {
  y := x - 1;
}
assert(y > 0);`
    },
    {
      name: "While Loop Example",
      code: `x := 0;
while (x < 4) {
  x := x + 1;
}
assert(x == 4);`
    },
    {
      name: "Bubble Sort",
      code: `for (i := 0; i < n; i := i + 1) {
  for (j := 0; j < n - i - 1; j := j + 1) {
    if (arr[j] > arr[j+1]) {
      temp := arr[j];
      arr[j] := arr[j+1];
      arr[j+1] := temp;
    }
  }
}
assert(for (i in range(n-1)):arr[i] <= arr[i+1]);`
    }
  ],
  equivalence: [
    {
      name: "Bubble Sort & Selection Sort",
      program1: `// Bubble Sort
for (i := 0; i < n; i := i + 1) {
  for (j := 0; j < n - i - 1; j := j + 1) {
    if (arr[j] > arr[j+1]) {
      temp := arr[j];
      arr[j] := arr[j+1];
      arr[j+1] := temp;
    }
  }
}`,
      program2: `// Selection Sort
for (i := 0; i < n; i := i + 1) {
  min_idx := i;
  for (j := i + 1; j < n; j := j + 1) {
    if (arr[j] < arr[min_idx]) {
      min_idx := j;
    }
  }
  temp := arr[min_idx];
  arr[min_idx] := arr[i];
  arr[i] := temp;
}`
    },
    {
      name: "Different Sum Algorithms",
      program1: `// Forward Sum
sum := 0;
for (i := 0; i < n; i := i + 1) {
  sum := sum + arr[i];
}`,
      program2: `// Backward Sum
sum := 0;
for (i := n - 1; i >= 0; i := i - 1) {
  sum := sum + arr[i];
}`
    }
  ]
};

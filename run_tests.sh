echo "Running Tests on Test Input..."
idris sorting.idr -o sorting
echo "Comparing Test Output..."
grep -v '^#' input.txt | ./sorting | grep -E "(\[|Permute)" > actual.txt
diff --strip-trailing-cr actual.txt expected.txt > diff.txt
if [[ $(wc -l < diff.txt) -ge "0" ]]
then
    echo "Tests Passed!"
else
    echo "Test Failed! Differences outputted to diff.txt"
fi
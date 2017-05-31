date
echo Repository at `git log --format=format:%H -n 1`
pushd ../lean/ > /dev/null
echo Lean       at `git log --format=format:%H -n 1`
popd  > /dev/null
find . -name "*.olean" -type f -delete
for file in natural_transformation.lean products/products.lean universal/universal.lean currying.lean
do 
    printf "Compiling %-40s " $file
    (time lean --make src/category_theory/$file)  2>&1 > /dev/null | grep real | awk '{print $2}'
done

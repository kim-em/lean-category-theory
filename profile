date | tee -a profile.out
echo Repository at `git log --format=format:%H -n 1` | tee -a profile.out
pushd ../lean/ > /dev/null
echo Lean       at `git log --format=format:%H -n 1` | tee -a profile.out
popd  > /dev/null
find . -name "*.olean" -type f -delete
for file in natural_transformation.lean products/default.lean universal/default.lean currying/currying_3.lean
do 
    printf "Compiling %-40s " $file  | tee -a profile.out
    (time lean --make src/category_theory/$file)  2>&1 > /dev/null | grep real | awk '{print $2}' | tee -a profile.out
done

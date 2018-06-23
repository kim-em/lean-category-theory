date | tee -a profile.out
echo Repository at `git log --format=format:%H -n 1` | tee -a profile.out
# find . -name "*.olean" -type f -delete
rm src/categories/currying/*.olean
for file in products/bifunctors.lean currying/currying_1.lean currying/currying_2.lean currying/currying_3.lean currying/currying_4.lean
do 
    printf "Compiling %-40s " $file  | tee -a profile.out
    (time lean --make src/categories/$file)  2>&1 > /dev/null | grep real | awk '{print $2}' | tee -a profile.out
done

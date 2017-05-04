find . -name "*.olean" -type f -delete
for file in natural_transformation.lean products/products.lean universal/universal.lean monoidal_category/drinfeld_centre.lean
do 
    printf "Compiling %-40s " $file
    (time lean --make $file)  2>&1 > /dev/null | grep real | awk '{print $2}'
done

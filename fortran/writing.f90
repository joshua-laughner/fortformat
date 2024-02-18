program writing

write(*, *) 'Logicals'

write(*, '(a1,l1,a1)') '|',.TRUE.,'|'
write(*, '(a1,l2,a1)') '|',.TRUE.,'|'
write(*, '(a1,l3,a1)') '|',.TRUE.,'|'
write(*, '(a1,l4,a1)') '|',.TRUE.,'|'
write(*, '(a1,l5,a1)') '|',.TRUE.,'|'

write(*, '(a1)') ' '
write(*, *) 'Decimal integers'

write(*, '(a1,i1,a1)') '|',42,'|'
write(*, '(a1,i2,a1)') '|',42,'|'
write(*, '(a1,i3,a1)') '|',42,'|'
write(*, '(a1,i4,a1)') '|',42,'|'
write(*, '(a1,i5,a1)') '|',42,'|'

write(*, '(a1)') ' '
write(*, *) 'Zero-padded decimal integers'
! Both errors
! write(*, '(a1,i1.3,a1)') '|',42,'|'
! write(*, '(a1,i2.3,a1)') '|',42,'|'
write(*, '(a1,i3.3,a1)') '|',42,'|'
write(*, '(a1,i4.3,a1)') '|',42,'|'
write(*, '(a1,i5.3,a1)') '|',42,'|'

write(*, '(a1,i3.3,a1)') '|',-42,'|'
write(*, '(a1,i4.3,a1)') '|',-42,'|'
write(*, '(a1,i5.3,a1)') '|',-42,'|'

write(*, '(a1)') ' '
write(*, *) 'Octal integers'

write(*, '(a1,o5,a1)') '|',42,'|'
write(*, '(a1,o5.3,a1)') '|',42,'|'
write(*, '(a1,o5,a1)') '|',-42,'|'
write(*, '(a1,o5.3,a1)') '|',-42,'|'

write(*, '(a1)') ' '
write(*, *) 'Hexadecimal integers'

write(*, '(a1,z5,a1)') '|',42,'|'
write(*, '(a1,z5.3,a1)') '|',42,'|'
write(*, '(a1,z5,a1)') '|',-42,'|'
write(*, '(a1,z5.3,a1)') '|',-42,'|'

write(*, '(a1)') ' '
write(*, *) 'Strings'

write(*, '(a1,a,a1)') '|','abc','|'
write(*, '(a1,a5,a1)') '|','abc','|'
write(*, '(a1,a5,a1)') '|','abcde','|'
write(*, '(a1,a5,a1)') '|','abcdef','|'
write(*, '(a1,a,a1)') '|','abcdefg','|'


write(*, '(a1)') ' '
write(*, *) 'Reals'

write(*, '(a1,f5.3,a1)') '|',-0.01,'|'
write(*, '(a1,f8.3,a1)') '|',3.14,'|'
write(*, '(a5,2pf8.3,a1)') ' 2p |',3.14,'|'
write(*, '(a5,-2pf8.3,a1)') '-2p |',3.14,'|'

write(*, '(a1)') ' '

write(*, '(a1,e12.3,a1)') '|',0.0314,'|'
write(*, '(a1,e12.3,a1)') '|',3.14,'|'
write(*, '(a1,e12.3,a1)') '|',3140.0,'|'
write(*, '(a1,e12.3,a1)') '|',3141.59,'|'
write(*, '(a5,1pe12.3,a1)') ' 1p |',3.14,'|'
write(*, '(a5,2pe12.3,a1)') ' 2p |',3.14,'|'
write(*, '(a5,-1pe12.3,a1)') '-1p |',3.14,'|'
write(*, '(a5,-2pe12.3,a1)') '-2p |',3.14,'|'
write(*, '(a1,e12.3e1,a1)') '|',3.14e5,'|'
write(*, '(a1,e12.3e1,a1)') '|',3.14e15,'|'

write(*, '(a1)') ' '

write(*, '(a1,d12.3,a1)') '|',3.14,'|'
write(*, '(a1,1pd12.3,a1)') '|',3.14,'|'
write(*, '(a1,2pd12.3,a1)') '|',3.14,'|'
write(*, '(a1,-1pd12.3,a1)') '|',3.14,'|'
write(*, '(a1,-2pd12.3,a1)') '|',3.14,'|'


write(*, '(a1)') ' '
write(*, '(a3,e7.3,a1)') '7 |',3.14,'|'
write(*, '(a3,e8.3,a1)') '8 |',3.14,'|'
write(*, '(a3,e9.3,a1)') '9 |',3.14,'|'
write(*, '(a3,e7.3,a1)') '7 |',-3.14,'|'
write(*, '(a3,e8.3,a1)') '8 |',-3.14,'|'
write(*, '(a3,e9.3,a1)') '9 |',-3.14,'|'
write(*, '(a1,e12.3e5,a1)') '|',3.14,'|'


write(*, '(a1)') ' '
write(*, '(a1,d12.3,a1)') '|',3.14d120,'|'
write(*, '(a1,e12.3,a1)') '|',3.14d120,'|'
write(*, '(a1,e12.3e5,a1)') '|',3.14d120,'|'
write(*, '(a1,1pe12.3,a1)') '|',3.1415,'|'


end program

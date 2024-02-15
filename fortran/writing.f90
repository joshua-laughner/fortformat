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
end program

#! nqp

# Here is how to read up on sprintf:
#
#   $ perldoc -f sprintf
#   $ man 3 sprintf
#
# And here are some existing tests to be inspired by:
#
#   https://github.com/mirrors/perl/blob/blead/t/op/sprintf.t#L176
#   https://github.com/perl6/roast/blob/master/S32-str/sprintf.t
#
# The first of those texts takes precedence over the second one.
# Unless otherwise specified, we're aiming for full coverage of
# the functionality mentioned in those two manpages.
#
# Here's how to incorporate new functionality:
#
#   1. Write a failing test (run it, see it fail)
#   2. Implement the functionality (run tests, see them pass)
#   3. Refactor
#
# Incidentally, this is how to build most software. TDD -- it
# works.
#
# Here's a rough list of what's implemented already:
#
#   %s
#   %d
#   right-justification with space padding
#   that star thingy
#
# Here's a rough (incomplete) list of what remains to be done:
#
#   %c
#   %u
#   %b
#   %B
#   %o
#   %x
#   %X
#   make sure bigints work properly
#   %e
#   %f
#   %g
#   %E, %G
#   precision or maximum width (.)
#   synonyms (%i %D %U %O %F)
#   format parameter index (1$ etc)
#   left-justify (-)
#   pad with zeros (0)
#   ensure leading "0" or "0b" etc (#)
#   %v
#
# Here's a list of things we will not be supporting, ever:
#
#   pointers (%p)
#   l-value trickery (%n)
#   size (using hh, h, j, l, q, L, ll, t, or z)

sub sprintf($format, *@arguments) {
    my $directive := /'%' $<size>=(\d+|'*')? $<letter>=(.)/;
    my $percent_directive := /'%' $<size>=(\d+|'*')? '%'/;
    my $star_directive := /'%*' (.)/;

    my $dircount :=
        +match($format, $directive, :global)           # actual directives
        - +match($format, $percent_directive, :global) # %% don't require arguments
        + +match($format, $star_directive, :global)    # the star wants one more arg
    ;
    my $argcount := +@arguments;

    nqp::die("Too few directives: found $dircount, fewer than the $argcount arguments after the format string")
        if $dircount < $argcount;

    nqp::die("Too many directives: found $dircount, but "
             ~ ($argcount > 0 ?? "only $argcount" !! "no")
             ~ " arguments after the format string")
        if $dircount > $argcount;

    my $argument_index := 0;

    sub infix_x($s, $n) {
        my @strings;
        my $i := 0;
        @strings.push($s) while $i++ < $n;
        nqp::join('', @strings);
    }

    sub next_argument() {
        @arguments[$argument_index++];
    }

    sub string_directive($size) {
        my $string := next_argument();
        infix_x(' ', $size - nqp::chars($string)) ~ $string;
    }

    sub intify($number_representation) {
        my $result;
        if $number_representation > 0 {
            $result := nqp::floor_n($number_representation);
        }
        else {
            $result := nqp::ceil_n($number_representation);
        }
        $result;
    }

    sub decimal_int_directive($size) {
        my $int := intify(next_argument());
        infix_x(' ', $size - nqp::chars($int)) ~ $int;
    }

    sub percent_escape($size) {
        infix_x(' ', $size - 1) ~ '%';
    }

    sub chr_directive($size) {
        infix_x(' ', $size - 1) ~ nqp::chr(next_argument());
    }

    my %directives := nqp::hash(
        '%', &percent_escape,
        's', &string_directive,
        'd', &decimal_int_directive,
        'c', &chr_directive
    );

    sub inject($match) {
        nqp::die("'" ~ ~$match<letter>
            ~ "' is not valid in sprintf format sequence '"
            ~ ~$match ~ "'")
            unless nqp::existskey(%directives, ~$match<letter>);

        my $directive := %directives{~$match<letter>};
        my $size := $match<size> eq '*' ?? next_argument() !! +$match<size>;
        $directive($size);
    }

    subst($format, $directive, &inject, :global);
}

my $die_message := 'unset';

sub dies_ok(&callable, $description) {
    &callable();
    ok(0, $description);
    return '';

    CATCH {
        ok(1, $description);
        $die_message := $_;
    }
}

sub is($actual, $expected, $description) {
    my $they_are_equal := $actual eq $expected;
    ok($they_are_equal, $description);
    unless $they_are_equal {
        say("#   Actual value: $actual");
        say("# Expected value: $expected");
    }
}

plan(21);

is(sprintf('Walter Bishop'), 'Walter Bishop', 'no directives' );

is(sprintf('Peter %s', 'Bishop'), 'Peter Bishop', 'one %s directive' );
is(sprintf('%s %s', 'William', 'Bell'), 'William Bell', 'two %s directives' );

dies_ok({ sprintf('%s %s', 'Dr.', 'William', 'Bell') }, 'arguments > directives' );
is($die_message, 'Too few directives: found 2, fewer than the 3 arguments after the format string',
    'arguments > directives error message' );

dies_ok({ sprintf('%s %s %s', 'Olivia', 'Dunham') }, 'directives > arguments' );
is($die_message, 'Too many directives: found 3, but only 2 arguments after the format string',
    'directives > arguments error message' );

dies_ok({ sprintf('%s %s') }, 'directives > 0 arguments' );
is($die_message, 'Too many directives: found 2, but no arguments after the format string',
    'directives > 0 arguments error message' );

is(sprintf('%% %% %%'), '% % %', '%% escape' );

dies_ok({ sprintf('%a', 'Science') }, 'unknown directive' );
is($die_message, "'a' is not valid in sprintf format sequence '%a'",
    'unknown directive error message' );

is(sprintf('<%6s>', 12), '<    12>', 'right-justified %s with space padding');
is(sprintf('<%6%>'), '<     %>', 'right-justified %% with space padding');

is(sprintf('<%*s>', 6, 12), '<    12>', 'right-justified %s with space padding, star-specified');
is(sprintf('<%*%>', 6), '<     %>', 'right-justified %% with space padding, star-specified');

is(sprintf('<%2s>', 'long'), '<long>', '%s string longer than specified size');

is(sprintf('<%d>', 1), '<1>', '%d without size or precision');
is(sprintf('<%d>', "lol, I am a string"), '<0>', '%d on a non-number');
is(sprintf('<%d>', 42.18), '<42>', '%d on a float');
is(sprintf('<%d>', -18.42), '<-18>', '%d on a negative float');

is(sprintf('%c', 97), 'a', '%c directive');
is(sprintf('%10c', 65), '         A', '%c directive with padding');
is(sprintf('%c%c%c', 187, 246, 171), '»ö«', '%c directive with non-asci codepoints');

#! nqp

# Here is how to read up on sprintf:
#
#   http://pubs.opengroup.org/onlinepubs/009695399/functions/sprintf.html
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
#   %c
#   %o
#   %x
#   %X
#   pad with zeros (0)
#   %u
#
# Here's a rough (incomplete) list of what remains to be done:
#
#   %b
#   %B
#   make sure bigints work properly
#   %e
#   %f
#   %g
#   %E, %G
#   precision or maximum width (.)
#   synonyms (%i %D %U %O %F)
#   format parameter index (1$ etc)
#   left-justify (-)
#   ensure leading "0" or "0b" etc (#)
#   %v
#
# Here's a list of things we will not be supporting, ever:
#
#   pointers (%p)
#   l-value trickery (%n)
#   size (using hh, h, j, l, q, L, ll, t, or z)

grammar sprintf::Grammar {
    token TOP {
        :my $*ARGS_USED := 0;
        ^ <statement>* $
    }
    
    method panic($msg) { nqp::die($msg) }
    
    token statement {
        [
        | <?[%]> [ [ <directive> | <escape> ]
            || <.panic("'" ~ nqp::substr(self.orig,1) ~ "' is not valid in sprintf format sequence '" ~ self.orig ~ "'")> ]
        | <![%]> <literal>
        ]
    }

    proto token directive { <...> }
    token directive:sym<b> { '%' <flags>* <size>? <sym> }
    token directive:sym<c> { '%' <flags>* <size>? <sym> }
    token directive:sym<d> { '%' <flags>* <size>? <sym> }
    token directive:sym<o> { '%' <flags>* <size>? <sym> }
    token directive:sym<s> { '%' <flags>* <size>? <sym> }
    token directive:sym<u> { '%' <flags>* <size>? <sym> }
    token directive:sym<x> { '%' <flags>* <size>? $<sym>=<[xX]> }

    proto token escape { <...> }
    token escape:sym<%> { '%' <flags>* <size>? <sym> }
    
    token literal { <-[%]>+ }
    
    token flags {
        | $<space> = ' '
        | $<plus>  = '+'
        | $<minus> = '-'
        | $<zero>  = '0'
        | $<hash>  = '#'
    }
    
    token size {
        [ \d+ | $<star>=['*'] ]
    }
}

class sprintf::Actions {
    method TOP($/) {
        my @statements;
        @statements.push( $_.ast ) for $<statement>;

        if $*ARGS_USED < +@*ARGS_HAVE {
            nqp::die("Too few directives: found $*ARGS_USED,"
            ~ " fewer than the " ~ +@*ARGS_HAVE ~ " arguments after the format string")
        }
        if $*ARGS_USED > +@*ARGS_HAVE {
            nqp::die("Too many directives: found $*ARGS_USED, but "
            ~ (+@*ARGS_HAVE > 0 ?? "only " ~ +@*ARGS_HAVE !! "no")
            ~ " arguments after the format string")
        }
        make nqp::join('', @statements);
    }

    sub infix_x($s, $n) {
        my @strings;
        my $i := 0;
        @strings.push($s) while $i++ < $n;
        nqp::join('', @strings);
    }

    sub next_argument() {
        @*ARGS_HAVE[$*ARGS_USED++]
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

    sub padding_char($st) {
        my $padding_char := ' ';
        $padding_char := '0' if $_<zero> for $st<flags>;
        make $padding_char
    }

    method statement($/){
        my $st;
        if $<directive> { $st := $<directive> }
        elsif $<escape> { $st := $<escape> }
        else { $st := $<literal> }
        my @pieces;
        @pieces.push: infix_x(padding_char($st), $st<size>.ast - nqp::chars($st.ast)) if $st<size>;
        @pieces.push: $st.ast;
        make nqp::join('', @pieces)
    }

    method directive:sym<b>($/) {
        
    }
    method directive:sym<c>($/) {
        make nqp::chr(next_argument())
    }
    method directive:sym<d>($/) {
        my $int := intify(next_argument());
        if $<size> {
            my $sign := $int < 0 ?? '-' !! '';
            $int := nqp::abs_i($int);
            $int := $sign ~ infix_x(padding_char($/), $<size>.ast - nqp::chars($int) - 1) ~ $int
        }
        make $int
    }
    method directive:sym<o>($/) {
        my $int := intify(next_argument());
        my $knowhow := nqp::knowhow().new_type(:repr("P6bigint"));
        make nqp::base_I(nqp::box_i($int, $knowhow), 8)
    }

    method directive:sym<s>($/) {
        make next_argument()
    }
    # XXX: Should we emulate an upper limit, like 2**64?
    # XXX: Should we emulate p5 behaviour for negative values passed to %u ?
    method directive:sym<u>($/) {
        my $int := intify(next_argument());
        my $knowhow := nqp::knowhow().new_type(:repr("P6bigint"));
        if $int < 0 {
                my $err := nqp::getstderr();
                nqp::printfh($err, "negative value '" 
                                ~ $int
                                ~ "' for %u in sprintf");
                $int := 0;
        }

        my $chars := nqp::chars($int);

        # Go throught tostr_I to avoid scientific notation.
        $int := nqp::box_i($int, $knowhow);
        make nqp::tostr_I($int)
    }
    method directive:sym<x>($/) {
        my $int := intify(next_argument());
        my $knowhow := nqp::knowhow().new_type(:repr("P6bigint"));
        $int := nqp::base_I(nqp::box_i($int, $knowhow), 16);
        make $<sym> eq 'x' ?? nqp::lc($int) !! $int
    }

    method escape:sym<%>($/) {
        make '%'
    }

    method literal($/) {
        make ~$/
    }

    method size($/) {
        make $<star> ?? next_argument() !! ~$/
    }
}

my $actions := sprintf::Actions.new();

sub sprintf($format, *@arguments) {
    my @*ARGS_HAVE := @arguments;
    return sprintf::Grammar.parse( $format, :actions($actions) ).ast;
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

plan(41);

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
is(sprintf('<%06s>', 'hi'), '<0000hi>', 'right-justified %s with 0-padding');
is(sprintf('<%06%>'), '<00000%>', 'right-justified %% with 0-padding');

is(sprintf('<%*s>', 6, 12), '<    12>', 'right-justified %s with space padding, star-specified');
is(sprintf('<%0*s>', 6, 'a'), '<00000a>', 'right-justified %s with 0-padding, star-specified');
is(sprintf('<%*%>', 6), '<     %>', 'right-justified %% with space padding, star-specified');
is(sprintf('<%0*%>', 5), '<0000%>', 'right-justified %% with 0-padding, star-specified');

is(sprintf('<%2s>', 'long'), '<long>', '%s string longer than specified size');

is(sprintf('<%d>', 1), '<1>', '%d without size or precision');
is(sprintf('<%d>', "lol, I am a string"), '<0>', '%d on a non-number');
is(sprintf('<%d>', 42.18), '<42>', '%d on a float');
is(sprintf('<%d>', -18.42), '<-18>', '%d on a negative float');
is(sprintf('<%03d>', 1), '<001>', '%d on decimal with 0-padding');
is(sprintf('<%03d>', -11), '<-11>', '%d on negative decimal with 0-padding (but nothing to pad)');
is(sprintf('<%04d>', -1), '<-001>', '%d on negative decimal with 0-padding');

is(sprintf('%c', 97), 'a', '%c directive');
is(sprintf('%10c', 65), '         A', '%c directive with space padding');
is(sprintf('%c%c%c', 187, 246, 171), '»ö«', '%c directive with non-asci codepoints');
is(sprintf('%06c', 97), '00000a', '%c directive with 0-padding');

is(sprintf('%o', 12), '14', 'simple %o');
is(sprintf('%o', 22.01), '26', 'decimal %o');
is(sprintf('%06o', 127), '000177', '%o with 0-padding');

is(sprintf('%x', 0), '0', 'simple %x');
is(sprintf('%x', 12), 'c', 'simple %x');
is(sprintf('%x', 22.01), '16', 'decimal %x');
is(sprintf('%X', 12), 'C', 'simple %X');
is(sprintf('%05x', 12), '0000c', '%x with zero-padding');
is(sprintf('%0*x', 4, 12), '000c', '%x with zero-padding, star-specified');
is(sprintf('%u', 12), '12', 'simple %u');
is(sprintf('%u', 22.01), '22', 'decimal %u');
is(sprintf("%u", 2**32), "4294967296", "max uint32 to %u");

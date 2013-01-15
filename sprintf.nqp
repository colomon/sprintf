#! nqp

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
        my $result := pir::new__Ps('StringBuilder');
        my $i := 0;
        nqp::push_s($result, ' ') while $i++ < $n;
        ~$result;
    }

    # NQPBUG: Can't use the actual prefix 'next' in a subname
    sub newt_argument() {
        @arguments[$argument_index++];
    }

    sub string_directive($size) {
        my $string := newt_argument();
        infix_x(' ', $size - nqp::chars($string)) ~ $string;
    }

    sub percent_escape($size) {
        infix_x(' ', $size - 1) ~ '%';
    }

    my %directives := nqp::hash(
        's', &string_directive,
        '%', &percent_escape,
    );

    sub inject($match) {
        nqp::die("'" ~ ~$match<letter>
            ~ "' is not valid in sprintf format sequence '"
            ~ ~$match ~ "'")
            unless nqp::existskey(%directives, ~$match<letter>);

        my $directive := %directives{~$match<letter>};
        my $size := $match<size>[0] eq '*' ?? newt_argument() !! +$match<size>[0];
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

plan(17);

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

// END OF THE GENERATED PART

// The tests are written manually
#[concordium_cfg_test]
mod tests {
    use super::*;
    use concordium_std::test_infrastructure::*;
    use std::io::Write;

    // This test writes the init data and reads it back.
    // Uncomment this test if you want to write the binary
    // data for making an actual call with concordium-client
    // NOTE: once uncommented, run is as [cargo test], so
    // it can write into a file
   // #[concordium_test]
    fn test_read_init_data() {
        let buyer_addr = AccountAddress([0u8; 32]);
        let setup =
            ConCert_Execution_Examples_Escrow_Setup::build_setup(PhantomData,
                                                                 Address::Account(buyer_addr));
        match std::fs::File::create("escrow_init_data.bin") {
            Ok(mut f) => {
                let param_bytes = concert_std::to_bytes(&setup);
                match f.write_all(&param_bytes) {
                    Ok(_) =>
                        match std::fs::read("escrow_init_data.bin") {
                            Ok(v) => {
                                let prg = Program::new();
                                let mut cur = Cursor::new(v);
                                match <ConCert_Execution_Examples_Escrow_Setup>::concert_deserial(&mut cur, &prg.__alloc) {
                                    Ok(p) => {
                                        claim_eq!(p, setup, "Wrong deserial result");
                                    },
                                    Err(e) => fail!("{:?}", e)
                                };
                            },
                            Err(e) => fail!("{:?}", e)
                        },
                    Err(e) => fail!("Cannot write file: {:?}", e)
                }
            },
            Err(e) => fail!("Cannot create file: {:?}", e)
        }
    }

    #[concordium_test]
    fn test_init() {
        // buyer_addr should be != seller_addr
        let buyer_addr = AccountAddress([0u8; 32]);
        let seller_addr = AccountAddress([1u8; 32]);
        let amount = 10;
        let data = Vec::new();
        let mut st = ContractStateTest::open(data);
        let mut ctx = InitContextTest::empty();
        let setup =
            ConCert_Execution_Examples_Escrow_Setup::build_setup(PhantomData,
                                                                 Address::Account(buyer_addr));
        let param_bytes = concert_std::to_bytes(&setup);
        ctx.set_parameter(&param_bytes);
        let slot_time = Timestamp::from_timestamp_millis(11);
        ctx.set_metadata_slot_time(slot_time);
        ctx.set_init_origin(seller_addr);


        // set up the logger so we can intercept and analyze them at the end.
        let mut logger = LogRecorder::init();

        // call the init function
        // amount must be even for init to succeed
        let out = contract_init(&ctx, Amount::from_micro_ccd(amount), &mut logger, &mut st);

        let res = match out {
            Ok(res) => res,
            Err(e) => fail!("Contract initialization failed: {:?}", e),
        };
        claim_eq!(res, ());
        let arena = bumpalo::Bump::new();
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        let deserial_state : ConCert_Execution_Examples_Escrow_State = <_>::concert_deserial(&mut st, &arena).expect("Deserialisation failed");
        let res =  match deserial_state {
            ConCert_Execution_Examples_Escrow_State::build_state(_, last_action, next_step, seller, buyer, seller_withdrawable, buyer_withdrawable) => {
                claim_eq!(last_action, slot_time.timestamp_millis(), "Wrong last_action:{:?}",last_action);
                match next_step {
                    ConCert_Execution_Examples_Escrow_NextStep::buyer_commit(PhantomData) => (),
                    _ => fail!("Wrong next_step"),
                }
                match seller {
                    Address::Account(a) => {
                        claim_eq!(a, seller_addr, "Wrong seller: {:?}", a);
                    },
                    _ => fail!("Not an account")
                };
                match buyer {
                    Address::Account(a) => {
                        claim_eq!(a, buyer_addr, "Wrong buyer: {:?}", a);
                    },
                    _ => fail!("Not an account")
                };
                claim_eq!(seller_withdrawable, 0, "Wrong seller_withdrawable: {:?}", seller_withdrawable);
                claim_eq!(buyer_withdrawable, 0, "Wrong buyer_withdrawable: {:?}", buyer_withdrawable);
            },
        };
    }

    #[concordium_test]
    fn test_receive() {
        let mut ctx = ReceiveContextTest::empty();
        let prg = Program::new();
        let mut data : Vec<u8> = Vec::new();
        let params = Option::Some(&ConCert_Execution_Examples_Escrow_Msg::commit_money(PhantomData));
        params.concert_serial(&mut data).expect("Serialisation failed");
        ctx.set_parameter(&data);
        let data_st : Vec<u8> = Vec::new();
        let buyer_addr = AccountAddress([0u8; 32]);
        let seller_addr = AccountAddress([1u8; 32]);
        let self_addr = ContractAddress {index: 0, subindex : 0};
        let amount = 10;
        let init_balance = 10;
        let slot_time = Timestamp::from_timestamp_millis(11);
        ctx.set_metadata_slot_time(slot_time);
        ctx.set_invoker(buyer_addr);
        ctx.set_sender(Address::Account(buyer_addr));
        ctx.set_self_address(self_addr);
        ctx.set_self_balance(concordium_std::Amount::from_micro_ccd(init_balance));
        let mut st = ContractStateTest::open(data_st);
        let v : ConCert_Execution_Examples_Escrow_State =
            ConCert_Execution_Examples_Escrow_State::build_state
            (PhantomData,
             0,
             &ConCert_Execution_Examples_Escrow_NextStep::buyer_commit(PhantomData),
             Address::Account(seller_addr),
             Address::Account(buyer_addr),
             0,
             0);
        v.concert_serial(&mut st).expect("Serialisation of failed");
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        // set up the logger so we can intercept and analyze them at the end.
        let mut logger = LogRecorder::init();
        let res: Result<ActionsTree, _> =
            contract_receive(&ctx, Amount::from_micro_ccd(amount), &mut logger, &mut st);
        let actions = match res {
            Err(e) => fail!("Contract receive failed, but it should not have: {:?}",e),
            Ok(actions) => actions,
        };
        claim_eq!(actions, ActionsTree::Accept, "Contract receive produced incorrect actions.");
        let arena = bumpalo::Bump::new();
        st.seek(SeekFrom::Start(0)).expect("Seek failed");
        let deserial_state : ConCert_Execution_Examples_Escrow_State = <_>::concert_deserial(&mut st, &arena).expect("Deserialisation failed");
        let res =  match deserial_state {
            ConCert_Execution_Examples_Escrow_State::build_state(_, last_action, next_step, seller, buyer, seller_withdrawable, buyer_withdrawable) => {
                claim_eq!(last_action, slot_time.timestamp_millis(), "Wrong last_action:{:?}",last_action);
                match next_step {
                    ConCert_Execution_Examples_Escrow_NextStep::buyer_confirm(PhantomData) => (),
                    _ => fail!("Wrong next_step"),
                }
                match seller {
                    Address::Account(a) => {
                        claim_eq!(a, seller_addr, "Wrong seller: {:?}", a);
                    },
                    _ => fail!("Not an account")
                };
                match buyer {
                    Address::Account(a) => {
                        claim_eq!(a, buyer_addr, "Wrong buyer: {:?}", a);
                    },
                    _ => fail!("Not an account")
                };
                claim_eq!(seller_withdrawable, 0, "Wrong seller_withdrawable: {:?}", seller_withdrawable);
                claim_eq!(buyer_withdrawable, 0, "Wrong buyer_withdrawable: {:?}", buyer_withdrawable);
            },
        };
    }
}

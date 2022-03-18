-- Manually appended VIEWS

view : Model -> Html StorageMsg
view model =
  div []
    [ viewInput "text" "Name" (name (currentEntry model)) (UpdateEntry << MsgName)
    , viewInput "password" "Password" (password (currentEntry model)) (UpdateEntry << MsgPassword)
    , viewInput "password" "Re-enter Password" (passwordAgain (currentEntry model)) (UpdateEntry << MsgPasswordAgain)
    , viewValidation model
    , button [onClick Add] [text "Ok"]
    , viewStorage model
    ]


viewInput : String -> String -> String -> (String -> msg) -> Html msg
viewInput t p v toMsg =
  input [ type_ t, placeholder p, value v, onInput toMsg ] []

viewValidation : Model -> Html msg
viewValidation model =
    div [ style "color" "red" ] (List.map text (errors model))

viewStorage : Model -> Html msg
viewStorage model =
  let renderEntry entry =
        case entry of
          Build_StoredEntry nm _ -> li [] [text nm]
  in
  div []
    [ ul [] (List.map (renderEntry << proj1_sig) (proj1_sig <| users model))]

-- MAIN

main : Program () Model StorageMsg
main =
  Browser.element
  { init = \f -> initModel
  , update = updateModel
  , view = view
  , subscriptions = \_ -> Sub.none}

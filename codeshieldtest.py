def calc_bonus(account_balance, is_active, years_employed, user_role):
    bonus = 0

    if is_active:
        if account_balance > 5000:
            bonus = 500
        elif account_balance > 2000:
            bonus = 250
        else:
            bonus = 100
        if years_employed > 5:
            bonus += 200
        elif years_employed > 2:
            bonus += 100
    if user_role == "admin":
        bonus += 300

    return bonus 
calc_bonus(7000,True,7,"admin")
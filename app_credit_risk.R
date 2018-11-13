library(shiny)
library(plotly)
library(tidyverse)
library(shinydashboard)

# ================================================================================= #
# =================================== Functions =================================== #
# ================================================================================= #


# Definition of the Black Scholes European Call formula to be used later
BScall <- function(V,D,Tm,sig,r,q){
  d1 <- (log(V/D) + ( r - q + sig^2/2 ) *Tm ) / ( sig * sqrt(Tm))
  d2 <- d1 - sig * sqrt(Tm)
  V * exp(-q*Tm)*pnorm(d1) - D * exp(-r*Tm) * pnorm(d2)
}

# Jump: [M]erton [O]ption [P]rice (Factorial is prespecified)
mop_fct <- function(spot, vol, mat, strike, r, lambdaa, m, v){
  price_element = 1
  price = 0
  n = 0
  lambda_dt = lambdaa * ( 1 + m) * mat
  gamma = log(1 + m)
  
  while (price_element > 0.00001) {
    r_tilde = r + (n * gamma) / mat - lambdaa * m
    vol_tilde = sqrt(vol * vol + n * v / mat)
    cond_price = BScall(spot, strike, mat, vol_tilde, r_tilde, 0)
    weight = exp(-lambda_dt) * (lambda_dt)^n / factorial(n)
    price_element = cond_price * weight
    price = price + price_element
    n = n + 1
  }
  
  price
}

mop <- Vectorize(mop_fct)

# Barrier:
d1_fct <- function(spot, vol, mat, interest, bound_or_strike){
  log(spot / bound_or_strike) + (interest + 0.5 * vol^2) * mat / (vol * sqrt(mat))
}
d1 <- Vectorize(d1_fct)

d2_fct <- function(spot, vol, mat, interest, bound_or_strike){
  d1(spot, vol, mat, interest, bound_or_strike) - vol*sqrt(mat)
}
d2 <- Vectorize(d2_fct)

f_lo_fct <- function(spot, vol, mat, interest, bound, bound_rate){
  spot_adj = bound^2/spot
  d1_1     = d1(spot, vol, mat, interest, bound)
  d1_2     = d1(spot_adj, vol, mat, interest, bound)
  r_tilde  = interest + 0.5 * vol^2
  factor   = (bound/spot)^(2*r_tilde/vol^2)
  ifelse(spot > bound, spot * (pnorm(d1_1) - factor * pnorm(d1_2)),bound*exp(-bound_rate*mat))
}
f_lo <- Vectorize(f_lo_fct)

c_lo_fct <- function(spot, vol, mat, strike, interest, bound, bound_rate){
  spot_adj      = bound^2/spot
  r_tilde_plus  = interest + 0.5 * vol^2
  r_tilde       = interest - 0.5 * vol^2
  factor_minus  = (bound/spot)^(2*r_tilde/(vol*vol))
  factor_plus   = (bound/spot)^(2*r_tilde_plus/(vol*vol))
  strike_factor = strike * exp(-interest * mat)
  d1_1          = d1(spot, vol, mat, interest, strike)
  d1_2          = d1(spot_adj, vol, mat, interest, strike)
  d2_1          = d1_1 - vol*sqrt(mat)
  d2_2          = d1_2 - vol*sqrt(mat)
  ifelse(bound < strike, spot * (pnorm(d1_1) - factor_plus * pnorm(d1_2)) -
                strike_factor * (pnorm(d2_1) - factor_minus * pnorm(d2_2)),0)
}
c_lo <- Vectorize(c_lo_fct)

#(V,D,Tm,sig,r,q)

c_lo_bs_fct <- function(spot, vol, mat, strike, interest, dividends, bound, bound_rate){
  spot_adj      = bound^2 / spot
  r_tilde       = interest - 0.5 * vol^2
  factor        = (bound / spot)^( 2 * r_tilde / vol^2)
  ifelse(bound < strike, BScall(spot, strike, mat, vol, interest, dividends) -
                  factor * BScall(spot_adj, strike, mat, vol, interest, dividends),0)
}
c_lo_bs <- Vectorize(c_lo_bs_fct)

# Book manipulation:
# (a) spot is not discounted by gamma.
B_m_fct <- function(spot, vol, mat, strike, interest, dividend, bound, bound_rate){
  r_hat        = interest - dividend - bound_rate
  gt           = exp(-bound_rate*mat)
  # spot_tilde   = spot*gt
  strike_tilde = strike*gt
  bound_tilde  = bound*gt
  exp(-dividend * mat) * (f_lo(spot, vol, mat, r_hat, bound_tilde, bound_rate) -
    c_lo_bs(spot, vol, mat, strike_tilde, r_hat, 0, bound_tilde, bound_rate))
}
B_m <- Vectorize(B_m_fct)

# Følgende giver kvalitativt resultaterne i bogen:
# (a) alpha i m_tilde indeholder kun renten
# (b) exp1 er ufølsom overfor bound_rate.
B_b_fct <- function(spot, vol, mat, interest, dividend, bound, bound_rate){
  b       = (log(bound / spot) - bound_rate * mat) / vol
  r_tilde = interest - dividend - bound_rate - 0.5 * vol * vol
  m       = r_tilde / vol
  m_tilde = sqrt(m^2 + 2*(interest - 0* bound_rate))
  exp1    = exp((m - m_tilde) * b) * exp(-0 * bound_rate * mat)
  exp2    = exp(2 * m_tilde * b)
  d1      = (b - m_tilde * mat) / sqrt(mat)
  d2      = (b + m_tilde * mat) / sqrt(mat)
  bound * exp1 * (pnorm(d1) + exp2 * pnorm(d2))
}
B_b <- Vectorize(B_b_fct)

# The next formula, is the final one, which prices bond payoffs in a barrier setting
B_fct <- function(spot, vol, mat, strike, interest, dividend, bound, bound_rate){
  B_m(spot, vol, mat, strike, interest, dividend, bound, bound_rate) +
    B_b(spot, vol, mat, interest, dividend, bound, bound_rate)
}
B <- Vectorize(B_fct)
  
# The stock price without dividends is a down-and-out-call
stock_fct <- function(spot, vol, mat, strike, interest, bound){
  spot_adj          = bound^2 / spot
  r_tilde           = interest - 0.5 * vol^2
  factor            = (bound/spot)^(2*r_tilde/vol^2)
  strike_factor     = strike * exp(-interest * mat)
  d1_1              = d1(spot, vol, mat, interest, strike)
  d1_2              = d1(spot_adj, vol, mat, interest, strike)
  d2_1              = d1_1 - vol * sqrt(mat)
  d2_2              = d1_2 - vol * sqrt(mat)
  d2_1_bound        = d2(spot, vol, mat, interest, bound)
  d2_2_bound        = d2(spot_adj, vol, mat, interest, bound)
  strike_over_bound = spot * (pnorm(d1_1) - factor * pnorm(d1_2)) -
    strike_factor * (pnorm(d2_1) - factor * pnorm(d2_2))
  bound_over_strike = strike_over_bound + (bound - strike) * exp(-interest * mat) *
  (pnorm(d2_1_bound) - factor * pnorm(d2_2_bound))
  ifelse(bound < strike, strike_over_bound, bound_over_strike)
}
stock <- Vectorize(stock_fct)

# Lelands endogenous barrier (ll for leland
l_beta  <- function(r, dividend, vol){
  mu    <- r - dividend
  kappa <- mu - 0.5 * vol^2
  return(-(kappa + vol * sqrt(kappa^2 + 2*r*vol^2))/(vol^2))
}
ll_beta <- Vectorize(l_beta)

l_gamma <- function(r, dividend, vol, tax){
  beta <- ll_beta(r,dividend,vol)
  return(beta/(beta-1)*(1-tax)/r)
}
ll_gamma <- Vectorize(l_gamma)

l_coupon <- function(spot, r, dividend, vol, tax, alpha){
  beta <- ll_beta(r,dividend,vol)
  gamma <- ll_gamma(r,dividend,vol,tax)
  return(spot * gamma^(-1) * (((1 - beta)*tax - alpha * beta * (1 - tax)) / tax)^(1/beta))
}
ll_coupon <- Vectorize(l_coupon)

l_barrier <- function(spot, r, dividend, vol, tax, alpha){
  gamma <- ll_gamma(r, dividend, vol, tax)
  coupon <- ll_coupon(spot, r, dividend, vol, tax, alpha)
  return(gamma * coupon)
}
ll_barrier <- Vectorize(l_barrier)

l_p <- function(spot, asset, r, dividend, vol, tax, alpha){
  beta    <- ll_beta(r, dividend, vol)
  barrier <- ll_barrier(spot, r, dividend, vol, tax, alpha)
  return((asset / barrier)^beta)
}
ll_p <- Vectorize(l_p)

l_debt <- function(spot, asset, r, dividend, vol, tax, alpha){
  p <- ll_p(spot, asset, r, dividend, vol, tax, alpha)
  barrier <- ll_barrier(spot, r, dividend, vol, tax, alpha)
  coupon  <- ll_coupon(spot, r, dividend, vol, tax, alpha)
  ifelse(asset <= barrier,
         return(barrier * (1 - alpha)),
         return(coupon / r * (1 - p) + (1 - alpha) * barrier * p)
  )
}
ll_debt <- Vectorize(l_debt)

l_equity <- function(spot, asset, r, dividend, vol, tax, alpha){
  p <- ll_p(spot, asset, r, dividend, vol, tax, alpha)
  barrier <- ll_barrier(spot, r, dividend, vol, tax, alpha)
  coupon  <- ll_coupon(spot, r, dividend, vol, tax, alpha)
  debt <- ll_debt(spot, asset, r, dividend, vol, tax, alpha)
  ifelse(asset <= barrier,
         return(0),
         return(asset + coupon * (1 - p) * tax / r - debt - alpha * barrier * p)
  )
}
ll_equity <- Vectorize(l_equity)

l_spread <- function(spot, asset, r, dividend, vol, tax, alpha){
  coupon <- ll_coupon(spot, r, dividend, vol, tax, alpha)
  debt <- ll_debt(spot, asset, r, dividend, vol, tax, alpha)
  return( 100 * (coupon/debt - r))
}
ll_spread <- Vectorize(l_spread)

# ================================================================================= #
# ====================================== UI ======================================= #
# ================================================================================= #

ui<-dashboardPage(
  dashboardHeader(title = 'Credit Risk Dashboard'),
  
  sidebar <- dashboardSidebar(
    sidebarMenu(id = 'mytabs',
      menuItem('Merton', tabName = 'merton', icon = icon('maxcdn')),
      menuItem('Merton with Jumps', tabName = 'jump', icon = icon('plane')),
      menuItem('Black Cox Barriers', tabName = 'barrier', icon = icon('barrier')),
      menuItem('Leland', tabName = 'leland', icon = icon('tax')),
      menuItem('CDS', tabName = 'cds', icon = icon('frog')),
      h3("Input Variables"),
      sliderInput("r",    "Interest rate",    min=0.00, max=0.30,  value= 0.05     ),
      sliderInput("q",    "Dividends",        min=0.00, max=0.50,  value= 0.00     ),
      sliderInput("v",    "Volatility",       min=0.00, max=0.40,  value= 0.20     ),
      sliderInput("jr",   "Junior Debt",      min=0,    max=100,   value= 50       ),
      sliderInput("sr",   "Senior Debt",      min=0,    max=100,   value= 50       ),
      sliderInput("mat",  "Time to maturity", min=1,    max=30,    value= 1        ),
      
      h3('Credit spread'),
      sliderInput('spot', 'Current spot price', min = 50, max = 200, value = 100 ),
      
      h3('Jump diffusion'),
      sliderInput('k',   'Mean jump size',   min=-0.5, max=0.5,   value= -0.2     ),
      sliderInput('jv',  'Jump variance',    min=0.00, max=0.5,   value= 0.16     ),
      sliderInput('lamb','Jump intensity',   min=0.00, max=0.9,   value= 0.4      ),
      
      h3('Barrier parameters'),
      sliderInput('bnd', 'Barrier',          min=50,   max=120,   value= 80       ),
      sliderInput('gam', 'Boundary growth rate', min = 0, max = 0.4, value = 0.1  ),
      
      h3('Leland parameters'),
      sliderInput('tax',  'Corporate tax',    min=0,    max=0.5,   value= 0.35     ),
      sliderInput('bcsts','Bankruptcy costs', min=0,    max=1,     value= 0.5      )
    )
  ),
    
  body <- dashboardBody(
    tabItems(
      tabItem(tabName = 'merton',
              h2("Analysis of credit spreads in the standard Merton model"),
              plotlyOutput("payoffs", height = '400px'),
              plotlyOutput("spr_sr",  height = '400px'),
              plotlyOutput("spr_jr",  height = '400px')
              
      ),
      
      tabItem(tabName = 'jump',
              h2('Analysis of credit spreads in the jump diffusion model'),
              plotlyOutput("j_payoffs", height = '400px'),
              plotlyOutput('jump_sr', height = '400px'),
              plotlyOutput('jump_jr', height = '400px')
      ),
      tabItem(tabName = 'barrier',
              h2('Analysis of credit spreads in the Black Cox Barrier model'),
              plotlyOutput("bc_payoffs", height = '400px'),
              plotlyOutput('bc_sr', height = '400px'),
              plotlyOutput('bc_jr', height = '400px')
      ),
      
      tabItem(tabName = 'leland',
              h2('Analysis of credit spreads in the Leland model'),
              plotlyOutput("ll_debt_equity", height = '400px'),
              plotlyOutput('ll_spread', height = '400px'),
              plotlyOutput('ll_coupon_barrier', height = '400px')
      )
    )
  ),
  
  dashboardPage(
    dashboardHeader(title = 'Simple tabs'),
    sidebar,
    body
  )
)

# ================================================================================= #
# ==================================== Server ===================================== #
# ================================================================================= #

server<-function(input, output){
  
# --------------------------------------------------------------------------------- #
# Varibles are made reactive

  r <-   reactive({ input$r   })
  q <-   reactive({ input$q   })
  v <-   reactive({ input$v   })
  jr <-  reactive({ input$jr  })
  sr <-  reactive({ input$sr  })
  mat <- reactive({ input$mat })
  
  # Spread variables
  time_to_mat <- seq(1, 30, 1)
  spot        <- reactive({ input$spot })
  
  # Jump variables
  k       <- reactive({ input$k     })
  lambdaa <- reactive({ input$lamb  })
  jv      <- reactive({ input$jv    })
  
  # Barrier parameters
  bnd     <- reactive({ input$bnd   })
  gam     <- reactive({ input$gam   })
  
  # Leland parameters
  
  tax     <- reactive({ input$tax   })
  bcsts   <- reactive({ input$bcsts })
# --------------------------------------------------------------------------------- #  
# ------------------------------------ Merton ------------------------------------- #  
# --------------------------------------------------------------------------------- #

  # Payoffs
  bs_eq  <- reactive({ round(BScall(s, jr() + sr(), mat(), v(), r(), q()),    2) })
  b_sr   <- reactive({ round(s -BScall(s, sr(), mat(), v(), r(), q()),        2) })
  b_jr   <- reactive({ round(BScall(s, sr(), mat(), v(), r(), q()) - bs_eq(), 2) })
  
  # Credit Spread: Senior bond payoffs
  b_sr_spread <- reactive({ spot() - BScall(spot(), sr(), time_to_mat, v(), r(), q())  })
  b_sr_p20    <- reactive({ spot() + 20 - BScall(spot() + 20, sr(), time_to_mat, v(), r(), q()) })
  b_sr_m20    <- reactive({ spot() - 20 - BScall(spot() - 20, sr(), time_to_mat, v(), r(), q()) })
  
  # Credit spread: Junior bond payoffs
  b_jr_spread <- reactive({ BScall(spot(), sr()  + 0  , time_to_mat, v(), r(), q()) -
                             BScall(spot(), sr() + jr(), time_to_mat, v(), r(), q()) })
  b_jr_p20    <- reactive({ BScall(spot() + 20, sr()  + 0 , time_to_mat, v(), r(), q()) -
                             BScall(spot() + 20, sr() + jr(), time_to_mat, v(), r(), q()) })
  b_jr_m20    <- reactive({ BScall(spot() - 20, sr()  + 0 , time_to_mat, v(), r(), q()) -
                             BScall(spot() - 20, sr() + jr(), time_to_mat, v(), r(), q()) })
  
  # Credit spread: Spreads
  sr_spread   <- reactive({ 100 * (1 / time_to_mat * log(sr() / b_sr_spread() ) - r())  })
  sr_sp_p20   <- reactive({ 100 * (1 / time_to_mat * log(sr() / b_sr_p20()    ) - r())  })
  sr_sp_m20   <- reactive({ 100 * (1 / time_to_mat * log(sr() / b_sr_m20()    ) - r())  })
  
  jr_spread   <- reactive({ 100 * (1 / time_to_mat * log(sr() / b_jr_spread() ) - r())  })
  jr_sp_p20   <- reactive({ 100 * (1 / time_to_mat * log(sr() / b_jr_p20()    ) - r())  })
  jr_sp_m20   <- reactive({ 100 * (1 / time_to_mat * log(sr() / b_jr_m20()    ) - r())  })
  
# --------------------------------------------------------------------------------- #  
# -------------------------------- Jump Diffusion --------------------------------- #  
# --------------------------------------------------------------------------------- #
  # Payoffs
  s <-   seq(1,200,1)
  j_eq  <- reactive({ mop(s, v(), mat(), sr() + jr(), r(), lambdaa(), k(), jv())  })
  j_sr  <- reactive({ s- mop(s, v(), mat(), sr(), r(), lambdaa(), k(), jv())      })
  j_jr  <- reactive({ mop(s, v(), mat(), sr()  + 0, r(), lambdaa(), k(), jv()) -
                       mop(s, v(), mat(), sr() + jr(), r(), lambdaa(), k(), jv()) })
  
  # Credit spreads: Senior bond payoffs
  j_sr_std  <- reactive({ spot() - mop(spot(), v(), time_to_mat, sr(), r(), lambdaa(), k(), jv())           })
  j_sr_p20  <- reactive({ spot() + 20 - mop(spot() + 20, v(), time_to_mat, sr(), r(), lambdaa(), k(), jv()) })
  j_sr_m20  <- reactive({ spot() - 20 - mop(spot() - 20, v(), time_to_mat, sr(), r(), lambdaa(), k(), jv()) })
  
  # Credit spreads: Junior bond payoffs  
  j_jr_std  <- reactive({mop(spot(), v(), time_to_mat, sr()  + 0, r(), lambdaa(), k(), jv()) -
      mop(spot(), v(), time_to_mat, sr() + jr(), r(), lambdaa(), k(), jv()) })  
  j_jr_p20  <- reactive({mop(spot() + 20, v(), time_to_mat, sr()  + 0, r(), lambdaa(), k(), jv()) -
          mop(spot() + 20, v(), time_to_mat, sr() + jr(), r(), lambdaa(), k(), jv()) })
  j_jr_m20  <- reactive({mop(spot() - 20, v(), time_to_mat, sr()  + 0, r(), lambdaa(), k(), jv()) -
      mop(spot() - 20, v(), time_to_mat, sr() + jr(), r(), lambdaa(), k(), jv()) })
  
  # Credit spreads: Spreads
  yj_sr_std  <- reactive({ 100 * (1 / time_to_mat * log(sr() / j_sr_std() ) - r())  })
  yj_sr_p20  <- reactive({ 100 * (1 / time_to_mat * log(sr() / j_sr_p20() ) - r())  })
  yj_sr_m20  <- reactive({ 100 * (1 / time_to_mat * log(sr() / j_sr_m20() ) - r())  })
  
  yj_jr_std  <- reactive({ 100 * (1 / time_to_mat * log(sr() / j_jr_std() ) - r())  })
  yj_jr_p20  <- reactive({ 100 * (1 / time_to_mat * log(sr() / j_jr_p20() ) - r())  })
  yj_jr_m20  <- reactive({ 100 * (1 / time_to_mat * log(sr() / j_jr_m20() ) - r())  })

# --------------------------------------------------------------------------------- #  
# ---------------------------------- BC Barriers ---------------------------------- #  
# --------------------------------------------------------------------------------- #
  
  s <- seq(25,200,1)
  
  # Payoffs
  bc_eq   <- reactive({ stock(s, v(), mat(), sr() + jr(), r(), bnd() )  })
  bc_sr   <- reactive({ B(s, v(), mat(), sr(), r(), q(), bnd(), gam() ) })
  bc_jr   <- reactive({ B(s, v(), mat(), jr(), r(), q(), bnd(), gam() ) })
  
  # The next four are for consideration only. Perhaps, perhaps not, to graph
  bc_m_sr <- reactive({ B_m(s, v(), mat(), sr(), r(), q(), bnd(), gam() ) })
  bc_b_sr <- reactive({ B_b(s, v(), mat(), jr(), r(), q(), bnd(), gam() ) })
  
  bc_m_sr <- reactive({ B_m(s, v(), mat(), sr(), r(), q(), bnd(), gam() ) })
  bc_m_jr <- reactive({ B_b(s, v(), mat(), jr(), r(), q(), bnd(), gam() ) })
  
  # Credit spreads: Payoffs
  bc_sr_std <- reactive({ B(spot(), v(), time_to_mat, sr(), r(), q(), bnd(), gam() ) })
  bc_sr_p20 <- reactive({ B(spot() + 20, v(), time_to_mat, sr(), r(), q(), bnd(), gam() ) })
  bc_sr_m20 <- reactive({ B(spot() - 20, v(), time_to_mat, sr(), r(), q(), bnd(), gam() ) })
  
  bc_jr_std <- reactive({ B(spot(), v(), time_to_mat, jr(), r(), q(), bnd(), gam() ) })
  bc_jr_p20 <- reactive({ B(spot() + 20, v(), time_to_mat, jr(), r(), q(), bnd(), gam() ) })
  bc_jr_m20 <- reactive({ B(spot() - 20, v(), time_to_mat, jr(), r(), q(), bnd(), gam() ) })
  
  # Credit spreads: Spreads
  bc_sr_c_std <- reactive({ 100 * ( log(sr() / bc_sr_std() ) / time_to_mat - r() ) })
  bc_sr_c_p20 <- reactive({ 100 * ( log(sr() / bc_sr_p20() ) / time_to_mat - r() ) })
  bc_sr_c_m20 <- reactive({ 100 * ( log(sr() / bc_sr_m20() ) / time_to_mat - r() ) })
  
  bc_jr_c_std <- reactive({ 100 * ( log(jr() / bc_jr_std() ) / time_to_mat - r() ) })
  bc_jr_c_p20 <- reactive({ 100 * ( log(jr() / bc_jr_p20() ) / time_to_mat - r() ) })
  bc_jr_c_m20 <- reactive({ 100 * ( log(jr() / bc_jr_m20() ) / time_to_mat - r() ) })
  
  # --------------------------------------------------------------------------------- #  
  # ------------------------------------- Leland ------------------------------------ #  
  # --------------------------------------------------------------------------------- #
  
  asset      <- seq(25,80,1)
  
  ll_dbt  <- reactive({ ll_debt(spot(), asset, r(), q(), v(), tax(), bcsts() )   })
  ll_eqt  <- reactive({ ll_equity(spot(), asset, r(), q(), v(), tax(), bcsts() ) })
  
  ll_cpn  <- reactive({ ll_coupon(asset, r(), q(), v(), tax(), bcsts() )         })
  ll_brr  <- reactive({ ll_barrier(asset, r(), q(), v(), tax(), bcsts() )        })

  ll_spd  <- reactive({ ll_spread(spot(), asset, r(), q(), v(), tax(), bcsts() ) })
  
# ================================================================================= #
# =================================== Plotting ==================================== #
# ================================================================================= #
  
  
# ---------------------------------- Merton --------------------------------------- #  

# The payoffs

  output$payoffs <- renderPlotly({
    gg <- ggplot(NULL, aes(x = s)) +
      geom_line(aes(y = bs_eq(), colour = 'Equity payoff')) +
      geom_line(aes(y = b_sr(), colour = 'Senior bond payoff')) +
      geom_line(aes(y = b_jr(), colour = 'Junior bond payoff')) +
      xlab('Spot price') +
      ylab('Payoff') +
      ggtitle("Payoff structure") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })

# --------------------------------------------------------------------------------- #
# The spreads
  
# Plotting of senior credit spreads
  output$spr_sr <- renderPlotly({
    ggplot(NULL, aes(x = time_to_mat)) +
      geom_line(aes(y = sr_spread(), colour = 'Senior bond spread')) +
      geom_line(aes(y = sr_sp_p20(), colour = 'Senior spread (spot + 20)')) +
      geom_line(aes(y = sr_sp_m20(), colour = 'Senior spread (spot - 20)')) +
      xlab('Time to maturity') +
      ylab('Credit spread (pct.)') +
      ggtitle("Risk structure of interest rates (senior bonds)") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })
  
# Plotting of junior credit spreads
  output$spr_jr <- renderPlotly({
    ggplot(NULL, aes(x = time_to_mat)) +
      geom_line(aes(y = jr_spread(), colour = 'Junior bond spread')) +
      geom_line(aes(y = jr_sp_p20(), colour = 'Junior spread (spot + 20)')) +
      geom_line(aes(y = jr_sp_m20(), colour = 'Junior spread (spot - 20)')) +
      xlab('Time to maturity') +
      ylab('Credit spread (pct.)') +
      ggtitle("Risk structure of interest rates (junior bonds)") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })
  

# ----------------------------------- Jumps --------------------------------------- #  

# The payoffs
  
  output$j_payoffs <- renderPlotly({
    gg <- ggplot(NULL, aes(x = s)) +
      geom_line(aes(y = j_eq(), colour = 'Equity payoff')) +
      geom_line(aes(y = j_sr(), colour = 'Senior bond payoff')) +
      geom_line(aes(y = j_jr(), colour = 'Junior bond payoff')) +
      xlab('Spot price') +
      ylab('Payoff') +
      ggtitle("Payoff structure") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })
  
# --------------------------------------------------------------------------------- #
# The spreads
  
# Plotting of senior credit spreads
  output$jump_sr <- renderPlotly({
    ggplot(NULL, aes(x = time_to_mat)) +
      geom_line(aes(y = yj_sr_std(), colour = 'Senior bond spread')) +
      geom_line(aes(y = yj_sr_p20(), colour = 'Senior spread (spot + 20)')) +
      geom_line(aes(y = yj_sr_m20(), colour = 'Senior spread (spot - 20)')) +
      xlab('Time to maturity') +
      ylab('Credit spread (pct.)') +
      ggtitle("Risk structure of interest rates (senior bonds)") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })
  
# Plotting of junior credit spreads
  output$jump_jr <- renderPlotly({
    ggplot(NULL, aes(x = time_to_mat)) +
      geom_line(aes(y = yj_jr_std(), colour = 'Junior bond spread')) +
      geom_line(aes(y = yj_jr_p20(), colour = 'Junior spread (spot + 20)')) +
      geom_line(aes(y = yj_jr_m20(), colour = 'Junior spread (spot - 20)')) +
      xlab('Time to maturity') +
      ylab('Credit spread (pct.)') +
      ggtitle("Risk structure of interest rates (junior bonds)") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })

# ----------------------------------- Barriers ------------------------------------ #  

# The payoffs

  output$bc_payoffs <- renderPlotly({
    gg <- ggplot(NULL, aes(x = s)) +
      geom_line(aes(y = bc_eq(), colour = 'Equity payoff')) +
      geom_line(aes(y = bc_sr(), colour = 'Senior bond payoff')) +
      geom_line(aes(y = bc_jr(), colour = 'Junior bond payoff')) +
      xlab('Spot price') +
      ylab('Payoff') +
      ggtitle("Payoff structure") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })
  
  # --------------------------------------------------------------------------------- #
  # The spreads
  
  # Plotting of senior credit spreads
  output$bc_sr <- renderPlotly({
    ggplot(NULL, aes(x = time_to_mat)) +
      geom_line(aes(y = bc_sr_c_std(), colour = 'Senior bond spread')) +
      geom_line(aes(y = bc_sr_c_p20(), colour = 'Senior spread (spot + 20)')) +
      geom_line(aes(y = bc_sr_c_m20(), colour = 'Senior spread (spot - 20)')) +
      xlab('Time to maturity') +
      ylab('Credit spread (pct.)') +
      ggtitle("Risk structure of interest rates (senior bonds)") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })
  
  # Plotting of junior credit spreads
  output$bc_jr <- renderPlotly({
    ggplot(NULL, aes(x = time_to_mat)) +
      geom_line(aes(y = bc_jr_c_std(), colour = 'Junior bond spread')) +
      geom_line(aes(y = bc_jr_c_p20(), colour = 'Junior spread (spot + 20)')) +
      geom_line(aes(y = bc_jr_c_m20(), colour = 'Junior spread (spot - 20)')) +
      xlab('Time to maturity') +
      ylab('Credit spread (pct.)') +
      ggtitle("Risk structure of interest rates (junior bonds)") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })
  
  
# ----------------------------------- Leland -------------------------------------- #  
  
  # The payoffs
  output$ll_debt_equity <- renderPlotly({
    gg <- ggplot(NULL, aes(x = asset)) +
      geom_line(aes(y = ll_eqt(), colour = 'Equity Value')) +
      geom_line(aes(y = ll_dbt(), colour = 'Bond Value')) +
      xlab('Asset value') +
      ylab('Instrument value (USD)') +
      ggtitle("Value structure") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })
  
  # Plotting of credit spreads
  output$ll_spread <- renderPlotly({
    ggplot(NULL, aes(x = asset)) +
      geom_line(aes(y = ll_spd(), colour = 'Credit spread')) +
      xlab('Firm asset value') +
      ylab('Credit spread (pct.)') +
      ggtitle("Risk structure of interest rates") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })
  
  # Coupon and credit barrier
  output$ll_coupon_barrier <- renderPlotly({
    ggplot(NULL, aes(x = asset)) +
      geom_line(aes(y = ll_cpn(), colour = 'Coupon')) +
      geom_line(aes(y = ll_brr(), colour = 'Default barrier')) +
      xlab('Firm asset value') +
      ylab('Value (USD)') +
      ggtitle("Structure of coupons and default barrier") +
      theme_classic() +
      theme(axis.text.x  = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust=.5, face="plain"),
            axis.text.y  = element_text(colour="grey20",size=10,angle=0, hjust= 1, vjust= 0, face="plain"),  
            axis.title.x = element_text(colour="grey20",size=10,angle=0, hjust=.5, vjust= 0, face="plain"),
            axis.title.y = element_text(colour="grey20",size=10,angle=90,hjust=.5, vjust=.5, face="plain"),
            legend.text  = element_blank(),
            legend.title = element_blank(),
            plot.title   = element_text(colour='grey20',size=15,angle=0, hjust=.5, vjust=.5, face='plain'))
  })
}

shinyApp(ui=ui, server=server)